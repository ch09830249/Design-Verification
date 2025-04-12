# AMBA
* **系統晶片中各個模組之間的連接通訊就通過匯流排**，總線就作為子系統之間共享的通訊鏈路。總線可以理解為數據傳輸的協議，大家都按照這種協議 (AHB、APB、AXI) 來傳數據，這樣各個模組之間就不會出錯，尤其是很多時候別人買你的 IP，你要保證人家買過去能用起來，那就需要一個規範來統一標準，我們稱之為總線
* 總線的優點就是成本低，方便使用。缺點也很明顯，就是會**造成效能瓶頸**，也正是因為這個所以匯流排協定一直在更新，到現在的 AXI4，讀寫資料通道分開，增加了資料的頻寬
* **AMBA 全名為 Advanced Microcontroller Bus Architecture** ，即匯流排協議標準 。AMBA 協定是與製程無關的，沒有電氣特性，而是一種協定。總共定義了**3 種**總線：
  * **AHB** (Advanced High-Performance Bus) (先進高效能匯流排, 用於高效能系統)
  * ASB（Advanced System Bus）用的很少
  * **APB** (Advanced Peripheral Bus) (進階週邊匯流排, 用於低速週邊)
* AMBA發展歷史：
  * AMBA1.0：ASB 和 APB
  * AMBA2.0: AHB、ASB 和 APB
  * AMBA3.0：**AMBA 高階可擴充介面 (AXI)**
  * AMBA4.0：....
## AMBA 匯流排的互連
![image](https://github.com/user-attachments/assets/04660363-cb87-40a2-b76b-e51f3c7d22bc)
* Arbiter 控制 mux 選擇哪個 master 有效。
* 選取了 master 之後，HADDR 會被**送進 Decoder 判斷選中的是那個 slave**
* 然後把對應 slave 的 **HSEL 訊號拉高**表示 slave 工作
* 接著**讀入位址**和**資料訊號** (PS: 這裡其他的 slave 其實也能看到資料和位址訊號，但因為他們的HSEL訊號沒被拉高，所以不會運作)  
**Note**: master 和 slave 中還有一對常用的 master 和 slave，就是 default master 和 default slave。當沒有 master 在工作的時候，就選擇 default master 來控制總線，這個 master 可以直接存取總線而不需要兩個仲裁週期的時間，他是最常用的 master。當沒有 slave 被控制的時候就選擇default slave 來被控制。
# Reference
AHB總線筆記（一）: https://www.bilibili.com/opus/639338820199776256  
AHB總線筆記（二）: https://www.bilibili.com/opus/639615918584889361?spm_id_from=333.1387.0.0
AHB匯流排筆記（三）附AMBA2.0面試提問: https://www.bilibili.com/opus/639640082077188135?spm_id_from=333.1387.0.0
