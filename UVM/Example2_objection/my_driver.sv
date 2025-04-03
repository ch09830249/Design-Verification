/*
    main_phase 是一個完整的任務，沒有理由只執行第一句，而後面的程式碼不執行。看起來似乎 main_phase 在執行的過程中被外力「殺死」了，
    事實上也確實如此。UVM 中透過 objection 機制來控制驗證平台的關閉。細心的讀者可能會發現，在上節的例子中，並沒有如2.2.1節所示明確地調用
    finish 語句來結束仿真。但是在運行上節範例時，模擬平台確實關閉了。在每個 phase 中，UVM 會檢查是否有 objection 被提起
    （raise_objection），如果有，那麼等待這個 objection 被撤銷（drop_objection）後停止模擬；如果沒有，則馬上結束當前 phase。
*/
class my_driver extends uvm_driver;

    `uvm_component_utils(my_driver)
    function new(string name = "my_driver", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("my_driver", "new is called", UVM_LOW);
    endfunction

    extern virtual task main_phase(uvm_phase phase);

endclass

task my_driver::main_phase(uvm_phase phase);
    phase.raise_objection(this);                                // 多加這個, 控制仿真的開始
    `uvm_info("my_driver", "main_phase is called", UVM_LOW);
    top_tb.rxd <= 8'b0;
    top_tb.rx_dv <= 1'b0;
    while(!top_tb.rst_n)
        @(posedge top_tb.clk);
    for(int i = 0; i < 256; i++) begin
        @(posedge top_tb.clk);
        top_tb.rxd <= $urandom_range(0, 255);
        top_tb.rx_dv <= 1'b1;
        `uvm_info("my_driver", "data is drived", UVM_LOW);
    end
    @(posedge top_tb.clk);
    top_tb.rx_dv <= 1'b0;
    phase.drop_objection(this);                                 // 和這個, 控制仿真的結束, 讀者可以簡單地將 drop_objection 語句當成是 finish 函數的替代者
endtask

/*
    raise_objection 語句必須在 main_phase 中第一個消耗模擬時間的語句之前。如 $display 語句是不消耗仿真時間的，這些語句可
    以放在 raise_objection 之前，但是類似 @posedge top.clk）等語句是要消耗模擬時間的。照如下的方式使用 raise_objection 是無法
    起到作用的
*/