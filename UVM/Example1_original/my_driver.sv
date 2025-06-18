/*
    向 rxd 發送 256 個隨機數據，並將 rx_dv 訊號置為高電平。當資料發送完畢後，將 rx_dv 訊號置為低電平
*/
class my_driver extends uvm_driver;

    function new(string name = "my_driver", uvm_component parent = null);   // 每一個派生自uvm_component或其派生類別的類別在其new函數中要指明兩個參數：name 和 parent
        super.new(name, parent);
    
    extern virtual task main_phase(uvm_phase phase);
endclass

task my_driver::main_phase(uvm_phase phase);
    top_tb.rxd <= 8'b0;                         // 清空 dut 的 input (rxd, rx_dv)   透過路徑取得 top_tb 的變數來控制 dut
    top_tb.rx_dv <= 1'b0;
    while(!top_tb.rst_n)                        // 等待 top_tb.rst_n 變為 1 (意謂著等到 reset 結束為止)
        @(posedge top_tb.clk);                  // clk 上沿回 while loop 檢查 !top_tb.rst_n
    for(int i = 0; i < 256; i++) begin          // 傳送 256 個 8 bits 數
        @(posedge top_tb.clk);                  // 當 clk 上沿
        top_tb.rxd <= $urandom_range(0, 255);   // 隨機產生 0 ~ 255 的數指定給 rxd (8 bits)
        top_tb.rx_dv <= 1'b1;                   // 並且指示該 rxd 有效
        `uvm_info("my_driver", "data is drived", UVM_LOW)   
        /*
            第一個參數是字串，可以想成 ID；第二個參數也是字串，是具體需要列印的資訊；第三個參數則是不重要程度。所以若比該 level 更高，代表更不重要，所以不需要印出
            UVM_LOW     => 極度重要
            UVM_MEDIUM
            UVM_HIGH    => 極度不重要
        */
    end
    @(posedge top_tb.clk);                      // 傳送完 256 個數, 將 rx_dv 設為 0, 代表不再傳送
    top_tb.rx_dv <= 1'b0;
endtask

/*
UVM_INFO                            表示這是一個 uvm_info 巨集列印的結果
my_driver.sv（18）                  指明此條列印資訊的來源，其中括號裡的數字表示原始的 uvm_info 列印語句在 my_driver.sv 中的行號
@48500000                           表示此訊息的列印時間
：drv                               這是 driver 在 UVM 樹中的路徑索引 (在 new my_dirver 的第一個參數)
[my_driver]                         方括號中顯示的資訊即呼叫 uvm_info 巨集時傳遞的第一個參數
data is drived
*/
