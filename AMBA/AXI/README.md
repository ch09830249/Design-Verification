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
  * **讀地址通道 (Read Address Channel)**
  * **寫入地址通道 (Write Address Channel)**
  * **讀數據通道 (Read Data Channel)**
  * **寫入資料通道 (Write Data Channel)**
  * **寫入響應通道 (Write Response Channel)**
## AXI的時序
為了理解 AXI 的讀寫時序, 首先需要理解基於 valid-ready 的握手機制, 然能理解 AXI 的讀/寫流程, 接著理解給出 AXI 所有接口信號的涵義。
最後理解 AXI 讀寫的時序圖,並以一個簡單的 AXI 接口的 block design 為例進行仿真,查看波形圖。
## AXI的握手機制
AXI 基於 valid-ready 的握手機制:
  * 發送方 (主 master) 透過置高 vaild 訊號表示位址/資料/控制訊息已準備好, 並保持在訊息總線上。  
    接收方 (從 slave) 透過置高 ready 訊號表示接收方已做好接收的準備。在 ACLK 上升沿, 若 vaild、ready 同時為高, 則進行資料傳輸
  * 每個 channel 都有自己的 handshake 機制，handshake 都是用 VALID/READY 來完成一次的傳輸。要傳輸資訊的一端不必等目的地是否有拉起 READY 就可以發送 VALID，但一旦發送 VALID 就必須等到目的地回 READY 才能結束 VALID。
  * VALID/READY handshake 機制可以有兩種做法:
    * 等有來源發送 VALID 後目的地若可以接收才回 READY。如下圖所示，T1 發送 VALID，T2 收到 VALID 後才回 READY，T3 完成此次的傳輸  
![image](https://github.com/user-attachments/assets/f243780c-065a-4ca3-bd42-1ebd4aadbe45)
    * 只要目的地可以接收資訊就一直拉著 READY。如下圖所示，T1 目的地可以接收資訊，T2 來源發送 VALID，T3 完成此次的傳輸  
![image](https://github.com/user-attachments/assets/6f1a9c0a-2152-4456-86bc-a421a1991e62)  

**注意 1**:  
valid 和 ready 無法互相依賴, 避免產生互相等待的死鎖, 通常建議 ready 和 valld 完全獨立, 這樣主從雙方都有終止通訊的能力。若想要從機接收全部的來自主機的數據, 可設 ready = H。  
**注意 2**  
依 valid ready 到達時間,可分為3種情況, 如右圖所示, 應注意到, 在 vaid 置高的同時,發送方就應該給出有效數據, 並將有效數據保持在總線, 而在之後的 ACLK 上升沿,若 vaiid ready均有效, 則應更新有效數據。
![image](https://github.com/user-attachments/assets/246e232e-20b0-4472-b4a1-1ef11d5e15a9)
![image](https://github.com/user-attachments/assets/fdbb5018-dfa7-4508-92cd-207056647714)
![image](https://github.com/user-attachments/assets/6415181d-6791-4092-b4a3-f0529999d8d7)
## 各 Channel Handshake Process 的訊號名稱
![image](https://github.com/user-attachments/assets/bc5c3e59-e840-4ad5-b23f-0c6546da1e77)

# AXI 讀寫流程
## 寫入操作
流程如圖, 涉及**寫入地址通道 AWC**、**寫入資料通道 DWC**、**寫入回應通道 WRC**
1. master 在**寫入地地址通道 AWC**上給予**寫入地址**和**控制資訊**
2. 在**寫入數據通道 DWC**上**傳輸數據**, AXI 的數據傳輸是突發性的, 一次可**傳輸多個數據**, 在傳輸最後一個數據時, 須同步給出 last 信號以表示數據傳輸即將終止。
3. slave 將在**寫入回應道 WRC**上給予寫入回應訊息, 對本次資料傳輸表示確認
![image](https://github.com/user-attachments/assets/9902e9e9-e173-476a-9cb2-df18d0ed2310)
## 讀取操作
讀取流程如圖, 涉及**讀取位址通道 ARC**、**讀取資料通道 DRC**
1. master 在**讀取位址通道 ARC**上給**讀取位址**和**控制訊息**
2. slave 將在**讀取資料通道 DRC**上給予資料。
Note: 讀取資料通道整合了讀取回應功能,且是從 slave 傳送給 master 的,在 slave 完成資料傳輸後, 會在讀取資料通道上給予回覆訊息, 標誌一次讀取結束。
![image](https://github.com/user-attachments/assets/aa6c9972-ba90-4684-a319-fc25d70c1b53)
# AXI-Full 的介面訊號
## 寫入地址通道 (Write Address Channel) 訊號
![image](https://github.com/user-attachments/assets/a6144be6-9512-4eeb-9d20-fa273f5f04d9)
![image](https://github.com/user-attachments/assets/400efd19-fa76-4cba-961f-8ce76ca6d0a2)
## 寫入資料通道 (Write Data Channel) 訊號
![image](https://github.com/user-attachments/assets/d11b9a4a-db8c-4e0a-8fbb-1d6c90ae01e3)
![image](https://github.com/user-attachments/assets/22e1a3ed-0908-445b-b6f1-e42e7aee8c05)
## 寫入響應通道 (Write Response Channel) 訊號
![image](https://github.com/user-attachments/assets/99066072-44cb-4a82-a4a9-54a94b880245)
![image](https://github.com/user-attachments/assets/9ff42c96-a95b-4e67-a5eb-ab5711fc7323)
## 讀地址通道 (Read Address Channel) 訊號
![image](https://github.com/user-attachments/assets/ba8a6fbf-159b-4a97-9383-b7c4e9fe3c12)
![image](https://github.com/user-attachments/assets/0ff120dd-83f7-46e8-b969-3603ba01d07b)
## 讀數據通道 (Read Data Channel) 訊號
![image](https://github.com/user-attachments/assets/f87e8491-28f5-4627-a195-61a05ef167fd)
![image](https://github.com/user-attachments/assets/4927911d-e90a-4a86-9a57-11a569325450)
# Reference
https://blog.csdn.net/qq_42622433/article/details/134070812
https://www.bilibili.com/video/BV1yP12YdErw/?spm_id_from=333.337.search-card.all.click
https://hackmd.io/@Ji0m0/S1aoQO-yt
https://blog.csdn.net/weixin_45243340/article/details/126067982
