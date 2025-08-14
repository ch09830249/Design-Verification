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
