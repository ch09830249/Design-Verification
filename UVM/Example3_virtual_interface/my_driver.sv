/*
    因為 my_driver 是一個類，在類中不能使用上述方式聲明一個 interface，只有在類似 top_tb 這樣的模組（module）中才可以。
    在類別中使用的是virtual interface：
*/
class my_driver extends uvm_driver;
    virtual my_if vif;
    `uvm_component_utils(my_driver)     // 將 my_driver 登記在 UVM 內部的一張表中
    function new(string name = "my_driver", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("my_driver", "new is called", UVM_LOW);
    endfunction

    extern virtual task main_phase(uvm_phase phase);

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("my_driver", "build_phase is called", UVM_LOW);
        if(!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
            `uvm_fatal("my_driver", "virtual interface must be set for vif!!!")
    endfunction
endclass

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