**AXI (Advanced eXtensible Interface 高階可擴充介面): AXI 是 AMBA 匯流排協定的一種, AMBA 是 ARM 公司 1996 年首次推出的微控制器匯流排協定。**
# 概述
# AXI 的三類接口
* 通常所說的 AXI 指 AXI4, 有三類介面:
  * AXI4-Full: 用於高效能記憶體映射需求
  * AXI4-Lite: 用於簡單的地吞吐量記憶體映射通訊(例如: 進出控制暫存器和狀態暫存暫存器)
  * AXI4-Stream: 用於高速流數據
* AXI 的特點
  * 高效率: 透過對 AXI 介面進行標準化, 開發人員只需學習用於 IP 的單一協定
  * 靈活:
    * AXI4 適用於記憶體映射接口, 僅一個地址階段就允許高達256個資料傳輸週期的高吞吐量爆發
    * AXI4-Lite 是一個輕量級的傳輸接口, 邏輯占用很小, 在設計和使用上都是一個簡單的接口
    * AXI4-Stream 完全取消了對位址階段的要求,並允許無限的資料突發大小。
## AXI的五個通道
* AXI4 和 AXI4-Lite 介面都有 5 個不同的通道組成, 每個通道都有若干個介面訊號。
  * **讀地址通道**
  * **寫入地址通道**
  * **讀數據通道**
  * **寫入資料通道**
  * **寫入響應通道**
## AXI的時序
為了理解 AXI 的讀寫時序, 首先需要理解基於 valid-ready 的握手機制, 然能理解 AXI 的讀/寫流程, 接著理解給出 AXI 所有接口信號的涵義。
最後理解 AXI 讀寫的時序圖,並以一個簡單的 AXI 接口的 block design 為例進行仿真,查看波形圖。
## AXI的握手機制
AXI 基於 valid-ready 的握手機制:
發送方(主 master)透過置高 vaild 訊號表示位址/資料/控制訊息已準備好,並保持在訊息總線上。
接收方(從 slave)透過置高 ready 訊號表示接收方已做好接收的準備。在 ACLK 上升沿,若vaild、ready同時為高, 則進行資料傳輸
**注意 1**:
valid 和 ready 無法互相依賴, 避免產生互相等待的死鎖, 通常建議 ready 和 valld 完全獨立, 這樣主從雙方都有終止通訊的能力。若想要從機接收全部的來自主機的數據, 可設ready=H。
**注意 2**
依 valid ready 到達時間,可分為3種情況, 如右圖所示, 應注意到, 在 vaid 置高的同時,發送方就應該給出有效數據, 並將有效數據保持在總線, 而在之後的 ACLK 上升沿,若 vaiid ready均有效, 則應更新有效數據。
![image](https://github.com/user-attachments/assets/246e232e-20b0-4472-b4a1-1ef11d5e15a9)
![image](https://github.com/user-attachments/assets/fdbb5018-dfa7-4508-92cd-207056647714)
![image](https://github.com/user-attachments/assets/6415181d-6791-4092-b4a3-f0529999d8d7)
# AXI 讀寫流程
## 寫入操作
