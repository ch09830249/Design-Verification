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
## AXI 的五個通道
* AXI4 和 AXI4-Lite 介面都有 5 個不同的通道組成, 每個通道都有若干個介面訊號。
  * **讀地址通道 AR (Read Address Channel)**
  * **讀數據通道 R (Read Data Channel)**
  * **寫入地址通道 AW (Write Address Channel)**
  * **寫入資料通道 W (Write Data Channel)**
  * **寫入響應通道 B (Write Response Channel)**
## AXI的時序
為了理解 AXI 的讀寫時序, 首先需要理解基於 valid-ready 的握手機制, 然能理解 AXI 的讀/寫流程, 接著理解給出 AXI 所有接口信號的涵義。
最後理解 AXI 讀寫的時序圖,並以一個簡單的 AXI 接口的 block design 為例進行仿真,查看波形圖。
## AXI 的握手機制
AXI 基於 valid-ready 的握手機制:
  * 發送方 (主 master) 透過**置高 vaild 訊號表示位址/資料/控制訊息已準備好, 並保持在訊息總線上**。
  * 接收方 (從 slave) 透過**置高 ready 訊號表示接收方已做好接收的準備**。
    * 在 ACLK 上升沿, 若 vaild、ready 同時為高, 則進行資料傳輸。
  * 每個 channel 都有自己的 handshake 機制，handshake 都是用 VALID/READY 來完成一次的傳輸。要傳輸資訊的一端不必等目的地是否有拉起 READY 就可以發送 VALID，但一旦發送 VALID 就必須等到目的地回 READY 才能結束 VALID。
  * VALID/READY handshake 機制可以有兩種做法:
    * 等有來源發送 VALID 後目的地若可以接收才回 READY。如下圖所示，T1 發送 VALID，T2 收到 VALID 後才回 READY，T3 完成此次的傳輸。  
      PS: 這裡的 valid 和 ready 同時為 1 且時長 1 週期的握手，稱為 1 次 Transfer。  
![image](https://github.com/user-attachments/assets/f243780c-065a-4ca3-bd42-1ebd4aadbe45)
    * 只要目的地可以接收資訊就一直拉著 READY。如下圖所示，T1 目的地可以接收資訊，T2 來源發送 VALID，T3 完成此次的傳輸。  
![image](https://github.com/user-attachments/assets/6f1a9c0a-2152-4456-86bc-a421a1991e62)
    * 來源和目的地同時在 T4 週期作用，完成一次數據傳輸（Transfer）。  
![image](https://github.com/user-attachments/assets/be4ed437-e796-45cb-af3a-ee1d7e617898)

**注意 1**   
source 和 destination 之間沒有任何關係。 當 source 有數據發送，拉高 valid 信號; 當 destination 可以接受數據，拉高 ready 信號。 source 和 destination 根據自己的情況拉高信號向對方表明意圖。   
**注意 2**  
為了避免 deadlock 產生，需要遵從 source 不能根據 destination 的 ready 信號來操作 valid 信號，但是 ready 信號可以根據 valid 信號來設置。  
**注意 3** 
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
* 為了看時序圖, 需要先了解 AXI 五個通道具體有哪些介面訊號
## 全域訊號
* ACLK
  * 所有訊號必須在時脈上升沿取樣
* ARESETn
AXI 使用低有效的重設訊號 ARESETn, 重設訊號可以非同步啟動
在重設過程中,適用於下列介面需求:
  * 主介面必須驅動 ARVALID, AWVALID 和 WVALID 為低
  * 從介面必須驅動 RVALID 和 BVALID 為低
  * 其他訊號可以被驅動為任意值。
  * 去使能後, 主介面的 Valid 變高至少要等 ARESETn 為 high 的上升沿邊緣。
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
# Channel 間的關係
Write response 必須要在最後一筆 write data 傳輸後才能回
Read data 必須要有 read address 傳輸後才能回
channel handshake 必須遵守下面的關係，其中單箭頭代表後者跟前著的關係沒有誰先誰後，雙箭頭代表前者一定要先發生後者才能發生
![image](https://github.com/user-attachments/assets/c8d49c72-23f5-4c90-bd0c-57e19b0e27ae)
上圖代表 read address channel 可以是 VALID 先拉起或 READY 先拉起，但 read address channel handshake 的訊號都必須要在 read data channel VALID 拉起前先拉起 (這其實也就是要傳輸 read data 前一定要先完成 read address 的傳輸)，而 read data channel 的 VALID 跟 READY 誰先拉起都可以。這邊並沒有要求 read data channel 的 READY 跟 read address channel 的 handshake 訊號的關係。
![image](https://github.com/user-attachments/assets/4fbec8ff-8300-40e1-a8c8-a681a7f62836)
上圖代表 write address channel 跟 write data channel 的 VALID 跟 READY 誰先拉起都可以，但這些訊號都必須在 write response channel 的 VALID 拉起前先拉起過 (這表示要有 write response 必須先完成 write address 跟 write data 的傳輸才行)，write response channel 的 VALID 跟 READY 誰先拉起都可以。

write data channel 另外需要注意的是 VALID 要看的是最後一筆 data 的 VALID。

另外，AXI3 的時候並沒有要求 write response channel 的 VALID 必須要在 write address channel handshake 完成之後，因為當時並沒有預期會有可能有 write response channel 拉起 VALID 但還沒有完成 write address 傳輸的情況。
# AXI-Full 的讀寫時序
## 時序圖圖例
了解各圖形的意義
![image](https://github.com/user-attachments/assets/3bc4621c-32c3-4441-8779-63f8568fa93f)
## 寫時序
* **Write Transcation: single data**
  * Manager 向 Subordinate 寫數據時，Manager 先發送寫位址，再發送寫數據，最後等待 Subordinate 的回應。
![image](https://github.com/user-attachments/assets/9368c5c3-c455-4cb0-8062-79beb64662e9)

* **Write Transcation: multi data**
  * 如圖所示, AXI4 協定主從設備間的寫入操作使用寫入位址、寫入資料和寫入回應通道。只需要一個位址就可以執行最大為 256 的 burst 長度的的寫入操作。
    * 1. 寫入位址: 寫入操作開始時, 主機發送位址和控制訊息到寫入位址通道。當位址通道上 AWVALID 和 AWREADY 同時為高時, 位置 A 會被有效的傳給設備, 然後主機將寫入資料到寫入資料頻道。
    * 2. 寫資料: 當 WREADY 和 WVALID 同時高的時候表示一個有效的寫資料。**當主機發發送最後一個資料時, WLAST 訊號變為高電位**
    * 3. 寫入回應: 當裝置接收完所有資料之後, 裝置會向主機發送一個寫入回應 BRESP 來表示寫交易完成, 當 BVALID 和 BREADY 同時為高的時候表示是有效的回應。
![image](https://github.com/user-attachments/assets/1248773e-a0a8-4116-95b6-e7027e3e3ed7)  
![image](https://github.com/user-attachments/assets/0e263f8f-9c25-441d-8085-35f9aebb3b17)
PS: 從第一個寫數據到最後一個寫數據（data1~data8），在一個 Transaction 中，整個 W 通道的數據過程稱為一次寫 Burst; 寫 Burst 內部每一拍的數據稱為一個寫 Beat。
## 讀時序
* **Read Transcation ： single data**
  * Manager 向 Subordinate 讀數據時，Manager 先發送讀位址，然後等待 Subordinate 的回應。
![image](https://github.com/user-attachments/assets/877eebb3-5d7b-4be8-9efe-fb4ba659afde)

* **Read Transcation ： multi data**
  * 如圖所示, AXI4 協定主從設備間的讀取操作使用獨立的讀取位址和讀取資料通道, 只需要一個位置就可以執行最大為 256 的 burst 長度的讀取操作。
    * 1. 讀取位址: 主機發送位址和控制訊息到讀取位址通道中, 當位址通道上 ARVALID 和 ARREADY 同時為高時, 位址 ARADDR 被有效的傳給設備, 之後設備輸出的資料將出現在讀取資料通道上
    * 2. 讀取資料: 當 RREADY 和 RVALID 同時為高的時候表示有效的資料傳輸, 從圖中可以看到傳輸了4個資料。為了顯示一次突發式讀寫的完成, 裝置以 RLAST 訊號變高電位來表示最後一個被傳送的數據。
D(A3) 是本次突發讀的最後一個讀取資料。
**Note**: 在資料讀取時, 讀取的資料從圖中可以看到不是連續讀取, 說明 slave 是空間時才傳遞
![image](https://github.com/user-attachments/assets/70e8df14-44d9-45e1-aac6-b297d6114b4f)
![image](https://github.com/user-attachments/assets/2df9a99a-a555-4f1e-97bd-aaad7a71fcae)
對比讀操作和寫操作的波形可以明顯看出讀寫通道的不對稱。 可以看到每一個讀數據都有一個匹配的讀回應伴隨，讀回應藉助讀數據通道返回。 而寫操作波形圖中，有專門的通道（B通道）進行寫操作的回應。
寫回應在寫數據操作完成之後返回一個寫回應，而對讀操作來說，伴隨著每個數據都有一個讀回應。 這也能體現兩者不對稱。
# Reference
漫談AMBA總線-AXI4[概述]: https://mp.weixin.qq.com/s?__biz=MzU1NzgxMDU3OQ==&mid=2247484239&idx=1&sn=bbfcc8352842d80045c1562cd13bdb6c&chksm=fc3155b3cb46dca5470f93ce1554122c0780be0637b123f889f885f05e6a18c93ac811924a8e&cur_album_id=2261926741449539597&scene=189#wechat_redirect  
https://blog.csdn.net/qq_42622433/article/details/134070812  
https://www.bilibili.com/video/BV1yP12YdErw/?spm_id_from=333.337.search-card.all.click  
https://hackmd.io/@Ji0m0/S1aoQO-yt  
https://blog.csdn.net/weixin_45243340/article/details/126067982  
