`include "my_transaction.sv"
class my_driver extends uvm_driver;
    virtual my_if vif;
    virtual my_if vif2;
    `uvm_component_utils(my_driver)

    function new(string name = "my_driver", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("my_driver", "new is called", UVM_LOW);
    endfunction

    extern virtual task main_phase(uvm_phase phase);
    extern virtual task drive_one_pkt(my_transaction tr);

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("my_driver", "build_phase is called", UVM_LOW);
        if(!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif)) 
            `uvm_fatal("my_driver", "virtual interface must be set for vif!!!")
        else
            `uvm_info("my_driver", "get virtual interface vif successfully!!!", UVM_LOW);
        if(!uvm_config_db#(virtual my_if)::get(this, "", "vif2", vif2))
            `uvm_fatal("my_driver", "virtual interface must be set for vif2!!!")
        else
            `uvm_info("my_driver", "get virtual interface vif2 successfully!!!", UVM_LOW);
    endfunction
endclass

task my_driver::main_phase(uvm_phase phase);
    my_transaction tr;
    // ......
    phase.raise_objection(this);
    `uvm_info("my_driver", "main_phase is called", UVM_LOW);
    for (int i = 0; i < 2; i++) begin
        tr = new("tr");
        assert(tr.randomize() with {pload.size == 20;});
        tr.print_tr();
        drive_one_pkt(tr);
    end
    // ......
    phase.drop_objection(this);
endtask

task my_driver::drive_one_pkt(my_transaction tr);
    bit [47:0] tmp_data;
    bit [7:0] data_q[$];

    // Push dmac to data_q
    tmp_data = tr.dmac;
    for (int i = 0; i < 6; i++) begin
        data_q.push_back(tmp_data[7:0]);        
        tmp_data = (tmp_data >> 8);
    end

    // Push smac to data_q (6 Bytes)
    tmp_data = tr.smac;
    for (int i = 0; i < 6; i++) begin
        data_q.push_back(tmp_data[7:0]);        
        tmp_data = (tmp_data >> 8);
    end

    // Push ether_type to data_q (2 Bytes)
    tmp_data = tr.ether_type;
    for (int i = 0; i < 2; i++) begin
        data_q.push_back(tmp_data[7:0]);        
        tmp_data = (tmp_data >> 8);
    end

    // Push payload to data_q (tr.pload.size Bytes)
    for (int i = 0; i < tr.pload.size; i+=8) begin
        for (int j = 0; j < 8; j++) begin
            data_q.push_back(tr.pload[i + j]);
        end      
    end

    // Push crc to data_q (4 Bytes)
    tmp_data = tr.crc;
    for (int i = 0; i < 4; i++) begin
        data_q.push_back(tmp_data[7:0]);
        tmp_data = (tmp_data >> 8);
    end

    // dmac + smac + ether_type + payload + crc

    `uvm_info("my_driver", "begin to drive one pkt", UVM_LOW);
    
    repeat(5) @(posedge vif.clk);

    while (data_q.size() > 0) begin
        @(posedge vif.clk);
        vif.valid <= 1'b1;
        vif.data <= data_q.pop_front();
    end

    @(posedge vif.clk);
    vif.valid <= 1'b0;
    `uvm_info("my_driver", "end drive one pkt", UVM_LOW);
endtask
