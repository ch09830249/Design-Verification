![image](https://github.com/user-attachments/assets/c205fffb-6216-4e4c-8c5b-148ec296ae6d)
## APB 總線特性
* **低速匯流排，低功耗**
* 介面簡單。在 bridge 中鎖存位址訊號和控制訊號。適用於多種週邊，採用上升沿觸發操作。
## APB 組成
* AHB2APB 橋
  * 可以鎖存所有位址、資料和訊號。
    * PS: 鎖存器 (Latch) 是一種對脈衝電平敏感的**儲存單元電路**，它們可以在特定輸入脈衝電平作用下改變狀態。鎖存，就是**把訊號暫存以維持某種電位狀態**。**鎖存器最主要的功能是緩存**，其次完成高速的控制器與慢速的周邊裝置的不同步問題，其次是解決驅動的問題，最後是解決一個I/O 口既能輸出也能輸入的問題。鎖存器是利用電平控制資料的輸入，它包括不帶啟用控制的鎖存器和帶啟用控制的鎖存器。
  * 進行二級譯碼來產生 APB 從設備選擇訊號，APB 有一個位址空間例如 0x5000_0000 ~ 0x6fff_ffff，其中又分為很多小的 APB 位址，例如 APB1~APB5。(看下面範例比較清楚)
      * 設備之間的通訊範例
        * 拿一個 CPU 控制 DMA 的過程舉例說明設備之間的通訊：
![image](https://github.com/user-attachments/assets/806d01b8-84ae-4598-ba22-0b6a8947f39e)
          * DMA 在系統中**主要扮演一個資料搬運的角色**，它可以取代 CPU 做資料遷移
          * DMA 有自己的位址空間，表格中的 Address 為偏移位址 offset (0x30000+offset)，從 DMA 基底位址開始的一些暫存器保存的一般為狀態，稱為**狀態暫存器**。
          * CPU 控制 DMA 搬移數據，先從 DMA 中讀 DMA 的 Status，如果讀取 DMA 是 ready 狀態，那麼就可以給 DMA 寫的 0x00 位址給 1 (Start)，然後告訴 DMA 資料搬運的起始位址（Source address) 和目的位址（Destination address），然後再告訴DMA搬運資料的數量。
          * 之後就可以把搬運資料的工作交給DMA，然後自己騰出手來做別的事。 CPU 控制 DMA 做資料搬運主要可以分為以下步驟：
            * step1: CPU 設定(來源位址)、(目的位址)、（大小）
            * step2: 啟動 DMA
            * step3: DMA 把資料從 memory1 傳送到 memory2
            * step4: DMA 向 CPU 發動中斷請求
            * step5: CPU 檢查 DMA 的狀態
    * APB總線上的所有其他模組都是APB從設備。
# APB 連接埠介紹
在介紹總線具體握手規則之前，需要先熟悉一下 APB 總線端口，APB的端口如下：
![image](https://github.com/user-attachments/assets/df62d5e5-4f5d-47be-8848-0883d0be88e9)  
![image](https://github.com/user-attachments/assets/10c1be32-aa69-4662-a2d9-43413116ae07)  
大致可以分為以下三組：
* **系統訊號**
  * PCLK (系統時脈)
  * PRESETn (系統重位，低有效)
* **master 訊號**
  * PADDR（位址訊號，確定讀取與寫入的位址，由裝置匯流排的 bridge 單元所驅動）
  * PSELx（選擇訊號，被拉出來接給搭載 APB 匯流排的 slave，選取 slave 時，PSELx 訊號拉高）(從譯碼器來的訊號，到每個匯流排從設備x)
  * PNEABLE（啟用訊號，在 PSELx 拉高一個週期後，必定拉高）
  * PWRITE（High: APB write access, Low: APB read acess）
  * PWRDATA（Write data） 
    Note: PRDATA 和PWDATA 最多 32 位元寬
* **slave 訊號**
  * PREADY（ready 為高時，代表著一次 APB 資料傳輸的結束）
  * PRDATA（讀取資料）
  * PSLVERR（錯誤資料，由 slave 發出，具體邏輯由 slave 內部決定，當 slave 發現內部邏輯出現故障，譬如狀態機狀態出錯、計數器數位異常等，slave 都可以​​使用內部邏輯故障，譬如狀態機狀態出錯、BmasterBmasterB，都可以使用內部邏輯也能將該訊號結束，否則就可以使用內部邏輯來完成這個訊號該次傳輸或做出其他因應策略）
# APB 寫入傳輸
![image](https://github.com/user-attachments/assets/98934dc7-6319-4ccf-99fd-8f67de8b4860)  
* 如文件所示，APB 的寫入分為 2 種情況：
  * **沒有等待狀態的寫入**
  * **有等待狀態的寫入**
* APB 和 AHB 最大的差異就是 **APB 不採用 pipeline 形式的寫讀方式**
  * 對於 APB 協定來說，最快的寫入或讀出一個資料的週期是 2 週期，**先給位址，再寫資料**；**或先給位址，再讀資料**。
* APB 協定文件中，將上述這種傳輸方式分為兩個階段（phase），**給位址的階段稱為 Set up phase**；緊接著下一週期 **PENABLE 訊號拉高，標誌著進入寫入/讀取資料的階段**，該階段稱為 **Access phase**
## Write with no wait states
![image](https://github.com/user-attachments/assets/e3523c56-7f6a-48d3-87ec-cb20ed0ae657)
一次沒有等待狀態的寫入傳輸如上圖所示，在規劃寫資料時
* 第一周期 PSEL 拉高，表示選取某個 slave，同時給予位址資訊 Addr1 和寫入資料資訊 Data1
* 緊接著下一週期，PENABLE 訊號拉高，PREADY 訊號也拉高，此時資料寫入完成
![image](https://github.com/user-attachments/assets/4d5533c5-8e27-4cec-818e-d894fb0347ed)  
沒有等待狀態的APB連續寫入波形如上圖所示（代碼見後文），筆者將資料分為了兩組，group1為APB slave的連接埠訊號，group2為APB接的單一連接埠SRAM訊號。在第一個週期，也就是Setup phase，psel訊號拉高，表示slave被選中，值得注意的是此時要將SRAM的寫訊號和啟用訊號同步拉高，因為我們寫的是一個no wait states的APB接口，資料要在第二週期寫進SRAM的話，就需要提前一拍拉高啟用訊號和寫訊號。然後到了第二週期，penable訊號拉高，pready訊號也拉高標誌著這次APB傳輸的結束。另外，也正是因為在setup phase我們把SRAM的en訊號和we訊號拉高了，因此在access phase資料傳輸結束的同時，資料也被寫入到SRAM中。
## Write with wait states
![image](https://github.com/user-attachments/assets/95ec0871-b4ab-46f4-9b54-844f412403b5)
![image](https://github.com/user-attachments/assets/b9d98834-7b49-4dea-916e-05a9cfa90ddc)  
在文件中，對有等待週期的APB寫入傳輸描述如上，即：
* 一開始的 setup phase 和 write with no wait 沒有區別，psel 拉高，penable 為低
* 緊跟著第二週期，penable 拉高之後，進入 access phase，進入 access phase 之後，penable 不會拉低，直到 pready 為高標誌著一次傳輸結束時，penable 才會隨著 pready 一起拉低  
**Note**: penable 等待 pready 拉高的這段等待時間為 additional cycles，在這個階段 PADDR、PWRITE、PSEL、PENABLE、PWDATA 都應該保持不變，可以說總線被 hold 住了
# APB 讀取傳輸
![image](https://github.com/user-attachments/assets/aff681a7-9bcb-4410-b46c-efdb4bba0c06)
* APB 的讀取傳輸也分為 2 種情況：
  * **沒有等待狀態的讀取**
  * **有等待狀態的讀取**
## Read with no wait states
![image](https://github.com/user-attachments/assets/b34ad471-252b-421e-95f0-502405350d05)
一次沒有等待狀態的讀取傳輸如上圖所示，讀取狀態和寫入狀態不同，寫資料時 PWRITE=1，**讀取資料時應該令 PWRITE=0** 計畫讀取資料時
* 第一周期 PSEL 拉高，表示選取某個 slave，同時給予位址資訊 Addr1
* 緊接著下一個週期，PENABLE 訊號拉高，在 PREADY 訊號也被拉出高，這時被讀出
![image](https://github.com/user-attachments/assets/fe0b0f54-5b7a-4a7b-97a7-a5a429ddf6dc)
上圖為連續讀取的APB傳輸波形圖，從第一次讀取資料可以看到，隨著 psel 訊號拉高，PWRITE=0 標誌著為讀取狀態，此時傳入位址給 APB 的 SRAM，SRAM 連接埠 en=1，we=0 標誌著 SRAM 為讀取模式，資料在下一週期從 SRAM 給到 prdata  
**Note**: APB 匯流排完成一次讀取傳輸或寫入傳輸之後，PADDR 和 PWRITE 不會改變，會一直維持到下一次的傳輸，這可以減少功耗  
spec中描述如下
![image](https://github.com/user-attachments/assets/61c4b110-4412-439b-aae2-d795bb6af96f)
# 程式碼
這裡有一個 Write 和 Read 都是 with no states 的 APB SRAM，因為含有 SRAM 部分，所以在 apb_sram 中需要例化一個單一連接埠 ram，單一連接埠 ram 程式碼如下：
## dpram
```
module spram_generic#(
    parameter ADDR_BITS = 7,        //outside input 10
    parameter ADDR_AMOUNT = 128,    //outside input 1024
    parameter DATA_BITS = 32        //outside input 32
)(
    input                      clk     ,
    input                      en      ,
    input                      we      ,
    input      [ADDR_BITS-1:0] addr    ,
    input      [DATA_BITS-1:0] din     ,

    output reg [DATA_BITS-1:0] dout
);
reg [DATA_BITS-1:0] mem [0:ADDR_AMOUNT-1];

always @(posedge clk)begin
    if(en)begin
        if(we == 1&#39;b1)begin
            mem[addr] &lt;= din;
        end
        else
            dout      &lt;= mem[addr];
    end
end
endmodule
```
## apb_sram
```
module apb_sram#(
    parameter ADDR_BITS = 9,
    parameter DATA_BITS = 32,
    parameter MEM_DEPTH = 512
)(
    input                       pclk    ,
    input                       prstn   ,

    input                       psel    ,
    input                       penable ,

    input   [ADDR_BITS-1:0]     paddr   ,
    input                       pwrite  ,
    input   [DATA_BITS-1:0]     pwdata  ,

    output                      pready  ,
    output  [DATA_BITS-1:0]     prdata
);

// write part
wire apb_write_setup;
reg  apb_ram_write;

assign apb_write_setup = (pwrite) &amp;&amp; (!penable) &amp;&amp; (psel);

always @(posedge pclk or negedge prstn)begin
    if(!prstn)begin
        apb_ram_write &lt;= 1&#39;b0;
    end
    else if(apb_write_setup)begin
        apb_ram_write &lt;= 1&#39;b1;
    end
    else if(pready)begin
        apb_ram_write &lt;= 1&#39;b0;
    end
end
// read part
wire apb_read_setup;
reg  apb_ram_read;
assign apb_read_setup = (!pwrite) &amp;&amp; (!penable) &amp;&amp; (psel);
always @(posedge pclk or negedge prstn)begin
    if(!prstn)begin
        apb_ram_read &lt;= 1&#39;b0;
    end
    else if(apb_read_setup)begin
        apb_ram_read &lt;= 1&#39;b1;
    end
    else if(pready)begin
        apb_ram_read &lt;= 1&#39;b0;
    end
end

assign pready = pwrite ? apb_ram_write : apb_ram_read;

wire mem_en,mem_we;
assign mem_en = apb_write_setup || apb_read_setup;
assign mem_we = apb_write_setup;

spram_generic #(
    .ADDR_BITS      (ADDR_BITS          ),
    .DATA_BITS      (DATA_BITS          ),
    .ADDR_AMOUNT    (2&lt;&lt;(ADDR_BITS-1)   )
)u_spram_generic(
    .clk    (pclk   ),
    .en     (mem_en ),
    .we     (mem_we ),
    .addr   (paddr  ),
    .din    (pwdata ),
    .dout   (prdata )
);

endmodule
```
```
`timescale 1ns/1ns
`define MEM_PATH u_apb_sram.u_spram_generic
module tb#(
    parameter ADDR_BITS = 9,
    parameter DATA_BITS = 32,
    parameter MEM_DEPTH = 512
)();

reg clk, rstn;
always #5 clk = ~clk;

reg                     psel, penable, pwrite;
reg     [DATA_BITS-1:0] pwdata, ref_data;
reg     [ADDR_BITS-1:0] paddr ;
wire                    pready;
wire    [DATA_BITS-1:0] prdata;

reg     [DATA_BITS-1:0] pwdata_rand;
reg     [DATA_BITS-1:0] prdata_read;

task apb_write;
input [ADDR_BITS-1:0] addr;
input [DATA_BITS-1:0] wdata;
begin
    @(posedge clk);#1;
    penable = 0; psel = 1; pwrite = 1; paddr = addr; pwdata = wdata;
    @(posedge clk);#1;
    penable = 1;
end
endtask

task apb_read;
input [ADDR_BITS-1:0] addr;
output [DATA_BITS-1:0] rdata;
begin
    @(posedge clk); #1;
    penable = 0; psel = 1; pwrite = 0; paddr = addr;
    @(posedge clk); #1;
    penable = 1;
    @(negedge clk); #1;
    rdata = prdata;
end
endtask

integer i,j;
initial begin
    clk     &lt;= 1&#39;b0;
    rstn    &lt;= 1&#39;b0;
    pwrite  &lt;= 1&#39;b1;
    psel    &lt;= 1&#39;b0;
    penable &lt;= 1&#39;b0;
    pwdata  &lt;= 32&#39;d0;
    repeat(2) @(posedge clk);
    rstn    &lt;= 1&#39;b1;
    repeat(3) @(posedge clk);
    // SRAM data initial
    for (i = 0; i &lt; MEM_DEPTH; i = i + 1)begin
        pwdata = $random();
        `MEM_PATH.mem[i] = pwdata;
    end
    repeat(5) @(posedge clk); #1;
    $display(&quot;\ncontinuous writing&quot;);
    // SRAM data continuous writing
    fork
        begin
            @(posedge clk);#1
            paddr = 32&#39;d0;
            for (j = 0; j &lt; 10; j = j + 1)begin
                repeat(2) @(posedge clk) #1;
                paddr = paddr + 1;
                @(negedge clk) #1;
                ref_data = `MEM_PATH.mem[paddr-1];
                $display(&quot;ref_data = %d, addr = %d&quot;, ref_data, paddr-1);
            end
        end
        begin
            for (i = 0; i &lt; 10; i = i + 1)begin
                pwdata_rand = $random();
                apb_write(paddr, pwdata_rand);
                $display(&quot;pwdata = %d&quot;, pwdata);
            end
        end
    join_none


    repeat(21) @(posedge clk);#1;
    penable = 1&#39;b0;psel = 1&#39;b0;pwrite = 1&#39;b0;

    repeat(5) @(posedge clk);#1;
    $display(&quot;\ncontinuous reading&quot;);
    //SRAM continuous reading
    fork
        begin
            @(posedge clk);#1;
            paddr = 32&#39;d0;
            for (j = 0; j &lt; 10; j = j + 1)begin
                repeat(2) @(posedge clk);#1;
                paddr = paddr + 1;
            end
        end
        begin
            for (i = 0; i &lt; 10; i = i + 1)begin
                apb_read(paddr, prdata_read);
                $display(&quot;prdata_read = %d&quot;, prdata_read);
            end
        end
    join
    penable = 0;psel = 0;

    repeat(5) @(posedge clk);#1;
    $display(&quot;\ncontinuos writing and reading&quot;);
    //SRAM continuous write and read
    fork
        begin
            @(posedge clk);#1;
            paddr = 32&#39;d0;
            for (j = 0; j &lt; 10; j = j + 1)begin
                repeat (4) @(posedge clk); #1;
                paddr = paddr + 1;
            end
        end
        begin
            for (i = 0; i &lt; 10; i = i + 1)begin
                pwdata_rand = $random();
                apb_write(paddr, pwdata_rand);
                apb_read(paddr, prdata_read);
                $display(&quot;write data is %d, read data is %d&quot;, pwdata_rand, prdata_read);
            end
        end
    join
    penable = 0;psel = 0;
    // finish simulation
    repeat(20) @(posedge clk);
    $finish();
end
initial begin
    $fsdbDumpfile(&quot;apb_sram.fsdb&quot;);
    $fsdbDumpvars(0);
end
apb_sram #(
    .ADDR_BITS(ADDR_BITS),
    .DATA_BITS(DATA_BITS),
    .MEM_DEPTH(MEM_DEPTH)
) u_apb_sram(
    .pclk   (clk    ),
    .prstn  (rstn   ),

    .psel   (psel   ),
    .penable(penable),
    .paddr  (paddr  ),
    .pwrite (pwrite ),
    .pwdata (pwdata ),
    .pready (pready ),
    .prdata (prdata )
);
endmodule
```
* 仿真結果如下
```
continuous writing
pwdata = 620927818
ref_data = 620927818, addr = 0
pwdata = 1557269945
ref_data = 1557269945, addr = 1
pwdata = 160312595
ref_data = 160312595, addr = 2
pwdata = 164115731
ref_data = 164115731, addr = 3
pwdata = 853295461
ref_data = 853295461, addr = 4
pwdata = 684074833
ref_data = 684074833, addr = 5
pwdata = 3684186807
ref_data = 3684186807, addr = 6
pwdata = 3432517785
ref_data = 3432517785, addr = 7
pwdata = 2635204666
ref_data = 2635204666, addr = 8
pwdata = 3102358129
ref_data = 3102358129, addr = 9

continuous reading
prdata_read = 620927818
prdata_read = 1557269945
prdata_read = 160312595
prdata_read = 164115731
prdata_read = 853295461
prdata_read = 684074833
prdata_read = 3684186807
prdata_read = 3432517785
prdata_read = 2635204666
prdata_read = 3102358129

continuos writing and reading
write data is 830211938, read data is 830211938
write data is 4063587044, read data is 4063587044
write data is 353623338, read data is 353623338
write data is 3201975421, read data is 3201975421
write data is 753819481, read data is 753819481
write data is 1925424101, read data is 1925424101
write data is 1994288109, read data is 1994288109
write data is 3836215497, read data is 3836215497
write data is 2695810113, read data is 2695810113
write data is 1472319919, read data is 1472319919
```
波形圖
* 連續10次寫入、連續10次讀取、連續10次讀寫波形如下
![image](https://github.com/user-attachments/assets/89fea5cf-6ec4-4be4-9eee-93f1528a8c64)

# Reference
https://cloud.tencent.com/developer/article/1689936  
https://cloud.tencent.com.cn/developer/article/1689936  
https://blog.csdn.net/TommiWei/article/details/134811535  
https://www.cnblogs.com/lyc-seu/p/12674520.html  
https://blog.csdn.net/weixin_42664351/article/details/124472487  
