class my_agent extends uvm_agent;

    my_sequencer sqr;
    my_driver drv;
    my_monitor mon;
    uvm_analysis_port #(my_transaction) ap;

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
        sqr = my_sequencer::type_id::create("sqr", this);
        drv = my_driver::type_id::create("drv", this);
    end
    mon = my_monitor::type_id::create("mon", this);
endfunction

/*
    在 uvm_driver 中有成員變數 seq_item_port，而在 uvm_sequencer 中有成員變數 seq_item_export，
    這兩者之間可以建立一個 “通道”，通道中傳遞的 transaction 類型就是定義 my_sequencer 和 my_driver 時指定的
    transaction 類型，這裡是 my_transaction，當然了，這裡並不需要明確地指定「通道」的類型，UVM 已經做好了。
    在 my_agent 中，使用 connect 函數把兩者連結在一起：
*/

function void my_agent::connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (is_active == UVM_ACTIVE) begin
        drv.seq_item_port.connect(sqr.seq_item_export);     // driver 中的 seq_item_port 和 sqr 中的 seq_item_export 連接在一起
    end
    ap = mon.ap;
endfunction
