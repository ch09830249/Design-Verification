class my_agent extends uvm_agent;

    my_driver drv;
    my_monitor mon;
    // 需要透過 agent 去取出 monitor 的 ap
    uvm_analysis_port #(my_transaction) ap;     // 建立 handle

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);

    `uvm_component_utils(my_agent)

endclass

function void my_agent::build_phase(uvm_phase phase);
    super.build_phase(phase);
    uvm_config_db#(uvm_active_passive_enum)::get(this, "", "is_active", is_active);
    if (is_active == UVM_ACTIVE) begin
        drv = my_driver::type_id::create("drv", this);
    end
    mon = my_monitor::type_id::create("mon", this);
endfunction

function void my_agent::connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    /*
        與 my_monitor 中的 ap 不同的是，不需要對 my_agent 中的 ap 進行實例化，而只需要在 my_agent 的 connect_phase 中將 monitor 的值
        賦給它，換句話說，這相當於是指向 my_monitor 的 ap 的指標
    */
    ap = mon.ap;
endfunction
