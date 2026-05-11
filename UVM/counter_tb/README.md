# 32-bit Up/Down Counter UVM Testbench

## 目錄

- [DUT 功能說明](#dut-功能說明)
- [專案結構](#專案結構)
- [UVM 架構說明](#uvm-架構說明)
  - [整體層次圖](#整體層次圖)
  - [Virtual Sequencer 與 Virtual Sequence](#virtual-sequencer-與-virtual-sequence)
  - [p_sequencer 使用方式](#p_sequencer-使用方式)
  - [Scoreboard 參考模型](#scoreboard-參考模型)
- [測試案例](#測試案例)
- [如何執行 Simulation](#如何執行-simulation)
  - [環境需求](#環境需求)
  - [編譯並執行單一測試](#編譯並執行單一測試)
  - [執行完整 Regression](#執行完整-regression)
  - [查看波形](#查看波形)
  - [清除產生的檔案](#清除產生的檔案)
- [Makefile 參數說明](#makefile-參數說明)

---

## DUT 功能說明

**檔案：** `rtl/counter.v`

32-bit 可程式化上/下計數器，具備以下行為：

| 訊號 | 方向 | 說明 |
|------|------|------|
| `clk` | input | 時脈 |
| `rst_n` | input | 非同步低態重置 |
| `reverse` | input | 單 cycle pulse，觸發計數方向立即反轉 |
| `min_val[31:0]` | input | 計數下限（含） |
| `max_val[31:0]` | input | 計數上限（含） |
| `count[31:0]` | output | 目前計數值 |
| `direction` | output | 目前方向：0 = 向上，1 = 向下 |

計數行為：

- **向上計數**：`min_val -> min_val+1 -> ... -> max_val`，到達 `max_val` 後自動反轉往下
- **向下計數**：`max_val -> max_val-1 -> ... -> min_val`，到達 `min_val` 後自動反轉往上
- `reverse == 1`（單 cycle pulse）：立即反轉方向，與邊界反轉獨立運作
- `min_val` / `max_val` 可在執行期間動態更改；count 超出新範圍時自動 clamp

---

## 專案結構

```
counter_tb/
├── README.md
├── rtl/
│   └── counter.v               DUT：32-bit up/down counter
└── tb/
    ├── Makefile                 xrun 建置腳本
    ├── counter_tb_top.sv        Top-level：時脈、DUT 例化、UVM 啟動、shm wave dump
    ├── counter_if.sv            Interface：DUT 與 TB 之間的訊號通道
    ├── counter_seq_item.sv      Sequence item：封裝一筆交易的資料
    ├── counter_sequencer.sv     Sequencer：含 p_sequencer 共用欄位 (cfg_min/max/reverse_cnt)
    ├── counter_driver.sv        Driver：將 item 驅動到 interface
    ├── counter_monitor.sv       Monitor：取樣 DUT 輸出並送往 scoreboard
    ├── counter_scoreboard.sv    Scoreboard：prev-cycle 參考模型 + 比對邏輯
    ├── counter_agent.sv         Agent：整合 driver / monitor / sequencer
    ├── counter_env.sv           Environment：整合 agent + scoreboard
    ├── counter_sequences.sv     Sub-sequences：reset / count / reverse / cfg / boundary
    ├── counter_vseq.sv          Virtual sequencer + virtual sequences
    └── counter_tests.sv         四個 UVM test
```

---

## UVM 架構說明

### 整體層次圖

```
UVM Test
  test_basic_count | test_reverse | test_range_change | test_stress
        |
        | starts vseq on
        v
Virtual Sequencer (counter_virtual_sequencer)
  uvm_declare_p_sequencer -> p_sequencer (vseq layer)
        |
        | runs
        v
Virtual Sequences (counter_base_vseq)
  vseq_basic_count | vseq_reverse | vseq_range_change | vseq_stress
        |
        | delegates to
        v
+-----------------------------------------------------------------------+
| counter_env                                                           |
|  +----------------------------------------------------------+         |
|  | counter_agent (UVM_ACTIVE)                               |         |
|  |                                                          |         |
|  |  [Sequencer] <--TLM--> [Driver]                          |         |
|  |  counter_sequencer          drives vif signals           |         |
|  |  p_sequencer (sub-seq)                                   |         |
|  |       |                                                  |         |
|  |       v                                                  |         |
|  |  [Sub-Sequences]  (counter_base_seq)                     |         |
|  |  reset | count | reverse | cfg | boundary                |         |
|  |                                                          |         |
|  |  [Monitor] ----analysis_port----> [Scoreboard]           |         |
|  |  samples every cycle            prev-cycle ref model     |         |
|  |                                 clamp + bounce check     |         |
|  +----------------------------------------------------------+         |
+-----------------------------------------------------------------------+
        |                        ^
        | drives                 | samples
        v                        |
  [Interface: counter_if]
  clk  rst_n  reverse  min_val  max_val  count  direction
        |
        v
  [DUT: counter.v]
  32-bit | min/max | reverse pulse | out-of-range clamp
```

### Virtual Sequencer 與 Virtual Sequence

本專案採用標準的 **virtual sequence** 設計模式，將測試場景的「編排邏輯」與「驅動細節」分離：

**`counter_virtual_sequencer`** 持有真實 sequencer 的 handle：

```systemverilog
class counter_virtual_sequencer extends uvm_sequencer;
    counter_sequencer counter_seqr;  // 指向 env 內的真實 sequencer
endclass
```

**`counter_base_vseq`** 透過 virtual sequencer 協調 sub-sequences：

```systemverilog
class counter_base_vseq extends uvm_sequence;
    `uvm_declare_p_sequencer(counter_virtual_sequencer)

    task run_seq(counter_base_seq seq);
        seq.start(p_sequencer.counter_seqr);  // 委派給真實 sequencer
    endtask
endclass
```

test 在 `connect_phase` 將 virtual sequencer 與 env 內的真實 sequencer 連線：

```systemverilog
function void connect_phase(uvm_phase phase);
    vseqr.counter_seqr = env.agent.sequencer;
endfunction
```

### p_sequencer 使用方式

本專案在**兩個層次**都使用了 `p_sequencer`：

**層次 1：Sub-sequence 讀取共用設定**

```systemverilog
class counter_base_seq extends uvm_sequence #(counter_seq_item);
    `uvm_declare_p_sequencer(counter_sequencer)
    // body() 中可直接使用：
    //   p_sequencer.cfg_min      目前設定的下限
    //   p_sequencer.cfg_max      目前設定的上限
    //   p_sequencer.reverse_cnt  已發出的 reverse pulse 計數
endclass
```

**層次 2：Virtual sequence 存取真實 sequencer**

```systemverilog
class counter_base_vseq extends uvm_sequence;
    `uvm_declare_p_sequencer(counter_virtual_sequencer)
    // body() 中可直接使用：
    //   p_sequencer.counter_seqr  -> 真實 sequencer handle
endclass
```

### Scoreboard 參考模型

`counter_scoreboard` 使用 **output-based / prev-cycle** 策略，避免 driver 與 monitor 之間的 1-cycle timing offset：

```
每個 cycle 做：
  用 prev_count + prev_dir + prev_reverse + prev_min + prev_max
    -> 計算本 cycle 應看到的 exp_count / exp_dir
    -> 與 item.count / item.direction 比對

  clamp 優先：
    if (prev_count < prev_min) exp_count = prev_min
    if (prev_count > prev_max) exp_count = prev_max

  正常計數：
    direction flip <- prev_reverse or boundary hit
    count += 1 or -= 1 with wrap-around
```

---

## 測試案例

| Test name | Virtual sequence | 驗證重點 |
|-----------|-----------------|----------|
| `test_basic_count` | `vseq_basic_count` | 基本上下計數、邊界自動 bounce，min=0 max=7，跑 32 cycles |
| `test_reverse` | `vseq_reverse` | 單 cycle `reverse` pulse 反轉方向，連續兩次 reverse |
| `test_range_change` | `vseq_range_change` | 執行期間動態修改 min/max（[0..5] -> [3..15] -> [10..12]），含 clamp 驗證 |
| `test_stress` | `vseq_stress` | 邊界壓力測試：反覆跨越 min/max + 隨機 reverse pulse |

Regression 結果（全部通過）：

```
test_basic_count    PASS:43   FAIL:0   ERROR:0
test_reverse        PASS:52   FAIL:0   ERROR:0
test_range_change   PASS:67   FAIL:0   ERROR:0
test_stress         PASS:157  FAIL:0   ERROR:0
```

---

## 如何執行 Simulation

### 環境需求

- Cadence Xcelium（xrun）23.x 或以上
- UVM 1.2（`-uvmhome CDNS-1.2`，隨 Xcelium 附帶）

### 編譯並執行單一測試

```bash
cd counter_tb/tb

# 預設跑 test_basic_count
make sim

# 指定測試與 random seed
make sim TEST=test_reverse       SEED=42
make sim TEST=test_range_change  SEED=100
make sim TEST=test_stress        SEED=7
```

### 執行完整 Regression

```bash
# 預設：每個 test 用不同固定 seed（1/2/3/4）
make regress

# 四個 test 全部用同一個 seed
make regress REGRESS_SEED=42

# 每個 test 各自指定 seed
make regress SEED_BASIC=10 SEED_REV=20 SEED_CFG=30 SEED_STRESS=40
```

注意：`make regress REGRESS_SEED=42` 中 `regress` 與 `REGRESS_SEED` 之間需要有空格，否則 make 會把整個字串當成 target 名稱。

### 查看波形

Simulation 結束後波形自動寫入 `counter_waves.shm/`（由 TB 內的 `$shm_open` / `$shm_probe("ASC")` 控制，涵蓋所有訊號與子模組）。

```bash
make waves          # 用 SimVision 開啟
# 或
simvision counter_waves.shm &
```

### 清除產生的檔案

```bash
make clean
```

---

## Makefile 參數說明

```bash
make sim TEST=<test_name> SEED=<integer>
```

| 參數 | 預設值 | 說明 |
|------|--------|------|
| `TEST` | `test_basic_count` | UVM test class 名稱 |
| `SEED` | `1` | `make sim` 用的 random seed，傳入 `+ntb_random_seed` |
| `REGRESS_SEED` | 未設定 | `make regress` 時讓四個 test 使用同一個 seed |
| `SEED_BASIC` | `1` | `make regress` 時 test_basic_count 的 seed |
| `SEED_REV` | `2` | `make regress` 時 test_reverse 的 seed |
| `SEED_CFG` | `3` | `make regress` 時 test_range_change 的 seed |
| `SEED_STRESS` | `4` | `make regress` 時 test_stress 的 seed |

| Target | 說明 |
|--------|------|
| `sim` | 編譯 + 執行（預設） |
| `compile` | 僅編譯 |
| `regress` | 依序執行全部 4 個測試 |
| `waves` | 用 SimVision 開啟波形 |
| `clean` | 刪除所有產生的檔案 |
| `help` | 顯示說明 |
