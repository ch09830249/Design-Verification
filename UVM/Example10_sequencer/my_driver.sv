class my_driver extends uvm_driver#(my_transaction);    // 由於 uvm_driver 也是一個參數化的類，應該在定義 driver 時指明此 driver 要驅動的 transaction 的類型
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

/*
    這樣定義的好處是可以直接使用 uvm_driver 中的某些預先定義好的成員變量，如 uvm_driver 中有成員變量 req，
    它的類型就是傳遞給 uvm_driver 的參數，在這裡就是 my_transaction，可以直接使用 req，所以 main phase 可以調整
*/
task my_driver::main_phase(uvm_phase phase);
    phase.raise_objection(this);
    vif.data <= 8'b0;
    vif.valid <= 1'b0;
    while(!vif.rst_n)
        @(posedge vif.clk);
    for(int i = 0; i < 2; i++) begin
        // req 的類別就是 my_transaction
        req = new("req");
        assert(req.randomize() with {pload.size == 200;});
        drive_one_pkt(req);
    end
    repeat(5) @(posedge vif.clk);
    phase.drop_objection(this);
endtask

// task my_driver::main_phase(uvm_phase phase);
//     my_transaction tr;
//     ......
//     for (int i = 0; i < 2; i++) begin
//         tr = new("tr");
//         assert(tr.randomize() with {pload.size == 200;});
//         drive_one_pkt(tr);
//     end
//     ......
// endtask

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