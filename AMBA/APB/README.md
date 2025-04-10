# APB連接埠介紹
在介紹總線具體握手規則之前，需要先熟悉一下APB總線端口，APB的端口如下：
![image](https://github.com/user-attachments/assets/df62d5e5-4f5d-47be-8848-0883d0be88e9)
大致可以分為以下三組：
* 系統訊號：PCLK (系統時脈)，PRESETn (系統重位，低有效)
* master 訊號
  * PADDR（位址訊號，確定讀取與寫入的位址）
  * PSELx（選購訊號，被拉出來接給搭載APB匯流排的slave，選取slave時，PSELx訊號拉高）
  * PNEABLE（啟用訊號，在PSELx拉高一個週期後，必定拉高）
  * PWRITE（設定訊號能， PITE 寫時為高讀取時，必定拉高）
  * PWRITE（設定時將有效訊號寫為高時設定為高讀取資料時）
* slave 訊號
  * PREADY（ready為高時，代表著一次APB資料傳輸的結束）
  * PRDATA（讀取資料）
  * PSLVERR（錯誤資料，由slave發出，具體邏輯由slave內部決定，當slave發現內部邏輯出現故障，譬如狀態機狀態出錯、計數器數位異常等，slave都可以​​使用內部邏輯故障，譬如狀態機狀態出錯、BmasterBmasterB，都可以使用內部邏輯也能將該訊號結束，否則就可以使用內部邏輯來完成這個訊號該次傳輸或做出其他因應策略）
# APB 寫入傳輸
![image](https://github.com/user-attachments/assets/98934dc7-6319-4ccf-99fd-8f67de8b4860)
* 如文件所示，APB的寫入分為 2 種情況：**沒有等待狀態的寫入**；**有等待狀態的寫入**
* APB 和 AHB 最大的差異就是 APB 不採用 pipeline 形式的寫讀方式，因此對於 APB 協定來說，最快的寫入或讀出一個資料的週期是兩週期，**先給位址，再寫資料**；**或先給位址，再讀資料**。
* APB 協定文件中，將上述這種傳輸方式分為兩個階段（phase），給位址的階段稱為 Set up phase；緊接著下一週期 PENABLE 訊號拉高，標誌著進入寫入/讀取資料的階段，該階段稱為 Access phase 。
# Reference
https://cloud.tencent.com/developer/article/1689936  
https://cloud.tencent.com.cn/developer/article/1689936  
https://blog.csdn.net/TommiWei/article/details/134811535  
https://www.cnblogs.com/lyc-seu/p/12674520.html  
https://blog.csdn.net/weixin_42664351/article/details/124472487  
