class my_driver extends uvm_driver#(my_transaction);
    virtual my_if vif;

    `uvm_component_utils(my_driver)
    function new(string name = "my_driver", uvm_component parent = null);
        super.new(name, parent);
        `uvm_info("my_driver", "new is called", UVM_LOW);
    endfunction

    extern virtual task main_phase(uvm_phase phase);
    extern virutal task drive_one_pkt(my_transaction tr);

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("my_driver", "build_phase is called", UVM_LOW);
        if(!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif)) 
            `uvm_fatal("my_driver", "virtual interface must be set for vif!!!")
    endfunction
endclass

task my_driver::main_phase(uvm_phase phase);
    phase.raise_objection(this);
    vif.data <= 8'b0;
    vif.valid <= 1'b0;
    while(!vif.rst_n)
        @(posedge vif.clk);
    while(1) begin
        seq_item_port.get_next_item(req);       // 向 sequencer 發送 transaction 請求, driver 會 block 直到取得 transaction
        drive_one_pkt(req);                     // req 指向收到的 transaction, 將 transaction 分解並驅動 DUT
        seq_item_port.item_done();              // 向 sequencer 返回一個 transaction 完成的標示     
    end
    repeat(5) @(posedge vif.clk);
    phase.drop_objection(this);
endtask

task my_driver::drive_one_pkt(my_transaction tr);
    bit [47:0] tmp_data;
    bit [7:0] data_q[$];

    data_size = tr.pack_bytes(data_q) / 8;

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