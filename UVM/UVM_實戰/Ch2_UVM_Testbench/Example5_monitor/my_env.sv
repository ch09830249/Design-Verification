class my_env extends uvm_env;

    my_driver drv;
    my_monitor i_mon;
    my_monitor o_mon;

    function new(string name = "my_env", uvm_component parent);
        super.new(name, parent);
        $display("my_env is new!!");
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        $display("my_env build phase!!");
        drv = my_driver::type_id::create("drv", this);
        // 一個用來監測 DUT 的輸入口，一個用來監測 DUT 的輸出口
        i_mon = my_monitor::type_id::create("i_mon", this);     // 當完成 monitor 的定義後，可以在 env 中進行實例化
        o_mon = my_monitor::type_id::create("o_mon", this);
    endfunction

    `uvm_component_utils(my_env)

endclass
