// 因為 driver 和 monitor 其實做的事情是一樣的 (signals => transaction, transaction => signals), 所以為了 code reuse
class my_agent extends uvm_agent;   // 所有的 agent 都要派生自 uvm_agent 類，且本身就是一個 component

    my_driver drv;
    my_monitor mon;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    extern virtual function void build_phase(uvm_phase phase);
    extern virtual function void connect_phase(uvm_phase phase);

    `uvm_component_utils(my_agent)  // 應該使用 uvm_component_utils 巨集來實作 factory 註冊

endclass

function void my_agent::build_phase(uvm_phase phase);
    super.build_phase(phase);
    /* 
        透過 config table 取得當前 agent 的模式, 並指定給成員變數 is_active
    */
    uvm_config_db#(uvm_active_passive_enum)::get(this, "", "is_active", is_active);
    /* 
        is_active 的值預設為 UVM_ACTIVE，在這種模式下，是需要實例化 driver 的。
        UVM_PASSIVE 模式在輸出埠上不需要驅動任何訊號，只需要監測訊號。在這種情況下，連接埠上是只需要 monitor 的，所以 driver 可以不用實例化。
    */
    if (is_active == UVM_ACTIVE) begin
        drv = my_driver::type_id::create("drv", this);
    end
    mon = my_monitor::type_id::create("mon", this);
endfunction

function void my_agent::connect_phase(uvm_phase phase);
    super.connect_phase(phase);
endfunction
