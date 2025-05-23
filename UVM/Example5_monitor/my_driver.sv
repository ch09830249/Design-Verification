class my_driver extends uvm_driver;
    virtual my_if vif;
    virtual my_if vif2;
    `uvm_component_utils(my_driver)
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
        if(!uvm_config_db#(virtual my_if)::get(this, "", "vif2", vif2))
            `uvm_fatal("my_driver", "virtual interface must be set for vif2!!!")
    endfunction
endclass

task my_driver::main_phase(uvm_phase phase);
    my_transaction tr;
    ......
    for (int i = 0; i < 2; i++) begin
        tr = new("tr");
        assert(tr.randomize() with {pload.size == 200;});
        drive_one_pkt(tr);
    end
    ......
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

    // Push smac to data_q
    …

    // Push ether_type to data_q
    …

    // Push payload to data_q
    …

    // Push crc to data_q
    tmp_data = tr.crc;
    for (int i = 0; i < 4; i++) begin
        data_q.push_back(tmp_data[7:0]);
        tmp_data = (tmp_data >> 8);
    end

    `uvm_info("my_driver", "begin to drive one pkt", UVM_LOW);
    repeat(3) @(posedge vif.clk);

    while (data_q.size() > 0) begin
        @(posedge vif.clk);
        vif.valid <= 1'b1;
        vif.data <= data_q.pop_front();
    end

    @(posedge vif.clk);
    vif.valid <= 1'b0;
    `uvm_info("my_driver", "end drive one pkt", UVM_LOW);
endtask