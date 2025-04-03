/*
    class my_driver extends uvm_driver;
        my_if drv_if;
        …
    endclass

    因為 my_driver 是一個類，在 class 中不能使用上述方式聲明一個 interface，只有在類似 top_tb 這樣的模組（module）中才可以。
    在 class 中使用的是 virtual interface：
*/
class my_driver extends uvm_driver;
    virtual my_if vif;                  // 聲明一個 virtual interface
    virtual my_if vif2;
    `uvm_component_utils(my_driver)
    function new(string name = "my_driver", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("my_driver", "new is called", UVM_LOW);
    endfunction

    extern virtual task main_phase(uvm_phase phase);

    virtual function void build_phase(uvm_phase phase);     // build_phase 在 new 函數之後 main_phase 之前執行, build_phase 是不消耗仿真時間的 (function)
        super.build_phase(phase);                           // 因為在其父類別的 build_phase 中執行了一些必要的操作，這裡必須顯式地呼叫並執行它
        `uvm_info("my_driver", "build_phase is called", UVM_LOW);
        /*
            在 config_db 機制中，分為 set 和 get 兩步驟操作。set 操作簡單地理解成是“ 寄信 ”，而 get 則相當於是“ 收信 ”
        */
        if(!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif)) 
            `uvm_fatal("my_driver", "virtual interface must be set for vif!!!")
        if(!uvm_config_db#(virtual my_if)::get(this, "", "vif2", vif2))
            `uvm_fatal("my_driver", "virtual interface must be set for vif2!!!")
        /*
        get:
            virtual my_if:  uvm_config_db#（virtual my_if）則是一個參數化的類，其參數就是要寄信的類型，這裡是 virtual my_if
            this:
            "":
            "vif":          必須和 set 第三個參數一致
            vif:            表示要把得到的 interface 傳遞給哪個 my_driver 的成員變數
        */
    endfunction
endclass

/* 
    原本在 DUT 中輸入埠賦值（top_tb.rx_dv <= 1'b1;）都是使用絕對路徑, 將 top_tb. 改成 vif.
*/
task my_driver::main_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("my_driver", "main_phase is called", UVM_LOW);
    vif.data <= 8'b0;
    vif.valid <= 1'b0;
    while(!vif.rst_n)
        @(posedge vif.clk);
    for(int i = 0; i < 256; i++) begin
        @(posedge vif.clk);
        vif.data <= $urandom_range(0, 255);
        vif.valid <= 1'b1;
        `uvm_info("my_driver", "data is drived", UVM_LOW);
    end
    @(posedge vif.clk);
    vif.rx_dv <= 1'b0;
    phase.drop_objection(this);
endtask