# CDC Async FIFO 驗證環境

## 檔案結構

```
cdc_fifo_tb/
├── async_fifo.v            # DUT：深度16、Gray Code pointer
├── cdc_fifo_if.sv          # Interface：雙 CB + 6條 SVA
├── cdc_fifo_pkg.sv         # Package：參數、transaction item
├── cdc_write_agent.sv      # Write Agent（Driver/Monitor/Agent）
├── cdc_read_agent.sv       # Read  Agent（Driver/Monitor/Agent）
├── cdc_scoreboard.sv       # Scoreboard：雙 TLM FIFO 非同步比對
├── cdc_env_seq_tests.sv    # Env + 全部 Sequence + 全部 Test
├── top_tb.sv               # Top：雙時脈產生、DUT 連線、run_test
└── Makefile                # VCS / Xcelium 編譯腳本
```

## 時脈設定

| 域     | 頻率     | 週期   |
|--------|---------|--------|
| WCLK   | 200 MHz | 5.0 ns |
| RCLK   | 133 MHz | 7.52 ns|

兩個時脈**完全非同步**（RCLK 刻意延遲 1ns 避免剛好對齊）。

## 執行方式

```bash
# 單一 test（VCS）
make vcs TEST=test_basic_rw

# 全部 regression（Xcelium）
make regression_xrun

# 可用的 test name
# test_basic_rw         基本寫後讀順序驗證
# test_full_boundary    WFULL 邊界 + 多寫入保護
# test_asymmetric_rate  寫快讀慢的非對稱速率
# test_stress           Back-to-back 填滿/清空壓力
# test_async_reset      兩端 reset 時機不同
```

## CDC 關鍵設計說明

### 為什麼需要兩個獨立的 Agent？

Write Agent 的 Driver/Monitor 全部用 `@(vif.write_cb)` 和 `WCLK` 同步。
Read Agent 的 Driver/Monitor 全部用 `@(vif.read_cb)` 和 `RCLK` 同步。
兩個 Agent **不能共用同一個時脈**，否則取樣時機錯誤。

### Scoreboard 為何用兩個 TLM FIFO？

Write Monitor 在 WCLK domain 觸發，Read Monitor 在 RCLK domain 觸發。
兩邊事件到達 Scoreboard 的時間**不確定**。
各自放進 `uvm_tlm_analysis_fifo` 排隊，再用 `get()` 依序比對，
確保先進先出的語意正確比對，不會因時序差異造成誤判。

### Gray Code Assertion 為何重要？

```systemverilog
$onehot(wptr_gray ^ $past(wptr_gray))
```

這條 assertion 驗證「每次 counter 遞增只有 1 個 bit 改變」。
如果 DUT 把二進位計數器直接跨域傳送（忘記轉 Gray Code），
這條 assertion 會在第一次 2→3（010→011，2 bits 同時變）時觸發。

### RTL 模擬看不到什麼？

RTL 模擬假設所有訊號只有 0 和 1，**不會出現 metastable 狀態**。
CDC 的 metastability 風險只能透過：
1. **設計審查**：確認使用了 Two-FF Synchronizer 或等效電路
2. **Static Timing Analysis (STA)**：確認 setup/hold margin 足夠
3. **Gate-level simulation + SDF**：含真實時序的模擬
4. **Formal CDC 工具**（如 Mentor Questa CDC、Synopsys SpyGlass）

這個 testbench 做的是功能層驗證——確認在「同步器正確工作」的前提下，
FIFO 的讀寫順序、full/empty 狀態、Gray Code 結構都正確。
