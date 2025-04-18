# Verilog 中 reg 和 wire 的差別
* wire
  * wire 表示直通，即輸入有變化，輸出馬上無條件地反映（如與、非閘的簡單連接）
  * wire 相當於實體連線
  * wire 使用在連續賦值語句中 (線型資料需要持續的驅動)
    * 在連續賦值語句中，表達式右側的計算結果可以立即更新表達式的左側。在理解上，相當於一個邏輯之後直接連了一條線，這個邏輯對應於表達式的右側，而這條線就對應於 wire
  * wire 若無驅動器連接，其值為z
* reg
  * reg 表示一定要有觸發，輸出才會反映輸入的狀態
  * reg 相當於儲存單元
  * reg 表示一定要有觸發，沒有輸入的時候可以保持原來的值，但不直接實際的硬體電路對應 (暫存器型資料保持最後一次的賦值)
  * reg 則使用在過程賦值語句（initial ，always）中
    * 在過程賦值語句中，表達式右邊的計算結果在某種條件的觸發下放到一個變數當中，而這個變數可以宣告成reg類型的
    * 根據觸發條件的不同，過程賦值語句可以建模不同的硬體結構
      * 如果這個條件是時脈的上升沿或下降沿，那麼這個硬體模型就是一個觸發器
      * 如果這個條件是某一訊號的高電平或低電平，那麼這個硬體模型就是一個鎖存器
      * 如果這個條件是賦值語句的高電平或低電平，那麼這個硬體模型就是一個鎖存器
      * 如果這個條件是賦值語句右側一個硬體模型就是一個組合邏輯
  * reg預設初始值為不定值x
  
      對組合邏輯輸出變量，可以直接用assign。即如果不指定為reg類型，那麼就預設為1位元wire類型，故無需指定1位元wire類型的變數。當然專門指定出wire類型，可能是多位或為使程式易讀。wire只能被assign連續賦值，reg只能在initial和always中賦值。

      輸入埠可以由wire/reg驅動，但輸入埠只能是wire；輸出埠可以是wire/reg類型，輸出埠只能驅動wire ；若輸出埠在過程區塊中賦值則為reg型，若在過程區塊外賦值則為net型（wire/tri）。用關鍵字inout宣告一個雙向埠, inout埠不能宣告為reg類型，只能是wire型別。

      預設訊號是wire類型，reg類型要申明。這裡所說的預設是指輸出訊號申明成output時為wire。如果是模組內部訊號，必須申明成wire或reg.

      對always語句而言，賦值要申明成reg，連續賦值assign的時候要用wire。

 

模組呼叫時 訊號類型決定方法總結如下：

 

•訊號可分為連接埠訊號和內部訊號。出現在連接埠清單中的訊號是連接埠訊號，其它的訊號為內部訊號。

•對於連接埠訊號，輸入埠只能是net類型。輸出埠可以是net類型，也可以是register類型。若輸出埠在過程區塊中賦值則為register型別；若在過程區塊外賦值(包含實例化語句），則為net型別。

•內部訊號類型與輸出埠相同，可以是net或register類型。判斷方法也與輸出埠相同。若在過程區塊中賦值，則為register型別；若在過程區塊外賦值，則為net型別。

•若訊號既需要在過程區塊中賦值，又需要在過程區塊外賦值。這種情況是有可能出現的，如決斷訊號。這時需要一個中間訊號轉換。

 

 

下面所列是常出的錯誤及對應的錯誤訊息(error message)

•用過程語句給一個net類型的或忘記宣告類型的訊號賦值。

           訊息：illegal …… assignment.

•將實例的輸出連接到聲明為register類型的訊號。

           訊息：<name> has illegal output port specification.

•將模組的輸入訊號宣告為register類型。

           訊息：incompatible declaration, <signal name> …

 
