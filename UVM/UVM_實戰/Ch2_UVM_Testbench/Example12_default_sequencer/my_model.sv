class my_model extends uvm_component;
    uvm_blocking_get_port #(my_transaction) port;
    uvm_analysis_port #(my_transaction) ap;

    extern function new(string name, uvm_component parent);
    extern function void build_phase(uvm_phase phase);
    extern virtual task main_phase(uvm_phase phase);

    `uvm_component_utils(my_model)
endclass

function my_model::new(string name, uvm_component parent);
    super.new(name, parent);
    `uvm_info("my_model", "my_model is new", UVM_LOW);
endfunction

function void my_model::build_phase(uvm_phase phase);
    super.build_phase(phase);
    `uvm_info("my_model", "main_phase is called", UVM_LOW);
    port = new("port", this);
    ap = new("ap", this);
endfunction

task my_model::main_phase(uvm_phase phase);
    my_transaction tr;
    my_transaction new_tr;
    super.main_phase(phase);
    while(1) begin
        port.get(tr);
        new_tr = new("new_tr");
        new_tr.copy(tr);
        `uvm_info("my_model", "get one transaction, copy and print it:", UVM_LOW)
        new_tr.print();
        ap.write(new_tr);
    end
endtask
