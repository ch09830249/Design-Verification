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
* APB 協定文件中，將上述這種傳輸方式分為兩個階段（phase），**給位址的階段稱為 Set up phase**；緊接著下一週期 **PENABLE 訊號拉高，標誌著進入寫入/讀取資料的階段**，該階段稱為 **Access phase**
## Write with no wait states
![image](https://github.com/user-attachments/assets/f3511fed-7a0e-4cb9-b167-31de72b5dbca)  
一次沒有等待狀態的寫入傳輸如上圖所示，在規劃寫資料時，第一周期PSEL拉高，表示選取某個slave，同時給予位址資訊Addr1和寫入資料資訊Data1，緊接著下一週期，PENABLE訊號拉高，PREADY訊號也拉高，此時資料寫入完成。
![image](https://github.com/user-attachments/assets/4d5533c5-8e27-4cec-818e-d894fb0347ed)  
沒有等待狀態的APB連續寫入波形如上圖所示（代碼見後文），筆者將資料分為了兩組，group1為APB slave的連接埠訊號，group2為APB接的單一連接埠SRAM訊號。在第一個週期，也就是Setup phase，psel訊號拉高，表示slave被選中，值得注意的是此時要將SRAM的寫訊號和啟用訊號同步拉高，因為我們寫的是一個no wait states的APB接口，資料要在第二週期寫進SRAM的話，就需要提前一拍拉高啟用訊號和寫訊號。然後到了第二週期，penable訊號拉高，pready訊號也拉高標誌著這次APB傳輸的結束。另外，也正是因為在setup phase我們把SRAM的en訊號和we訊號拉高了，因此在access phase資料傳輸結束的同時，資料也被寫入到SRAM中。
## Write with wait states
![image](https://github.com/user-attachments/assets/bb1c8eeb-8714-4322-9092-2dfdc48fdc4f)  
![image](https://github.com/user-attachments/assets/b9d98834-7b49-4dea-916e-05a9cfa90ddc)  
在文件中，對有等待週期的APB寫入傳輸描述如上，即：

        一開始的setup phase和write with no wait沒有區別，psel拉高，penable為低；緊跟著第二週期，penable拉高之後，進入access phase，進入access phase之後，penable不會拉低，直到pready為高標誌著一次傳輸結束時，penable才會隨著pready一起拉低。 penable等待pready拉高的這段等待時間為additional cycles，在這個階段PADDR、PWRITE、PSEL、PENABLE、PWDATA都應該保持不變，可以說總線被hold住了。
# Reference
https://cloud.tencent.com/developer/article/1689936  
https://cloud.tencent.com.cn/developer/article/1689936  
https://blog.csdn.net/TommiWei/article/details/134811535  
https://www.cnblogs.com/lyc-seu/p/12674520.html  
https://blog.csdn.net/weixin_42664351/article/details/124472487  
