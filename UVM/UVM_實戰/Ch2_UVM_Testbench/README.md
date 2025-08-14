# Command line
## 執行 uvm
xrun -uvm top_tb.sv dut.sv  
| 部分          | 說明                                                       |
| ----------- | -------------------------------------------------------- |
| `xrun`      | Cadence 的模擬工具 Xcelium 的執行命令。                             |
| `-uvm`      | 啟用 UVM 驗證架構（會自動載入 `uvm_pkg` 等必要庫）。                       |
| `top_tb.sv` | 你的 **測試平台（Testbench）** 的頂層模組，通常負責例化 UVM 環境、DUT，以及啟動測試流程。 |
| `dut.sv`    | 你的 **設計模組（DUT，Design Under Test）**，也就是你想要驗證的電路或模組。       |

## Dump wave
1. 在 testbench 加入以下程式碼（產生 .shm）
```
initial begin
    $shm_open("waves.shm");        // 指定 SHM 波形檔名
    $shm_probe("AS");              // 把 top_tb 裡所有訊號都 dump 出來
end
```
2. xrun -uvm -access +r top_tb.sv dut.sv

| Flag               | 功能                            |
| ------------------ | ----------------------------- |
| `-access +r`       | 允許讀取信號，以便產生波形                 |
3. 仿真結束後，打開 SimVision
如果你加了 -gui，仿真完會自動打開 SimVision 並載入 waves.shm。如果沒有自動打開，可以手動執行：
```
simvision waves.shm
```
## $shm_probe 的語法與參數
```
$shm_probe([<depth>], [<scope>], [<signal_spec>]);
or
$shm_probe(<flags>, [<scope>]);
```
```
$shm_open("waves.shm");            // 開啟 shm 波形檔案
$shm_probe("AS", top_tb);          // 把 top_tb 所有信號都 dump 出來（推薦）
```

**flags：控制 dump 類型與深度（字串）** 
| Flag | 意思                            |
| ---- | ----------------------------- |
| `A`  | dump 所有信號（All signals）        |
| `S`  | 包含 `struct` 裡面的欄位（Structures） |
| `F`  | dump full 層級（等於層級 = 0）        |
| `C`  | dump 所有階層的 `clocking blocks`  |
| `+`  | 新增到已 dump 的信號                 |
| `-`  | 從已 dump 的清單中移除信號              |

通常用 "AS" 就夠用了，表示「所有訊號 + struct 支援」。  

**scope：要 dump 的模組/範圍**  
* 是一個模組名、instance、或 hierarchy 的識別符號（不是字串）
* 可以是例如：top_tb、top_tb.u_dut、env.agent.driver
```
$shm_probe("AS", top_tb);        // dump top_tb 的所有訊號
$shm_probe("AS", top_tb.u_dut);  // 只 dump u_dut
```

