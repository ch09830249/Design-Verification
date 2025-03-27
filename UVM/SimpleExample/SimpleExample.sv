`include "uvm_macros.svh"
import uvm_pkg::*;

// Interface : 用來連接 UVM 驗證環境 & DUT
interface axi_if(input logic clk);

    logic [31:0] addr;
    logic [31:0] data;
    logic valid;
    logic ready;

    modport drv (output addr, data, valid, input ready);
endinterface

// UVM transaction。描述 AXI 傳輸一次的訊息
class axi_transaction extends uvm_sequence_item;

    rand bit [31:0] addr;
    rand bit [31:0] data;

    `uvm_object_utils(axi_transaction) // 透過 uvm_object_utils 向 factory 註冊該 class (uvm_object 的子類都要)

    function new(string name = "axi_transaction");  // PS: 一定要再定義一個以 name 為參數的 constructor
        super.new(name);
    endfunction

endclass

class axi_sequence extends uvm_sequence #(axi_transaction); //這個axi_sequence是指繼承uvm_sequence，且產生的事務類型是axi_transaction

    `uvm_object_utils(axi_sequence) 

    function new(string name = "axi_sequence");
        super.new(name);
    endfunction

    task body();                // 定義了如何產生並且傳送 transaction => sequencer => driver
        axi_transaction txn;    // 建立一個 transaction 的 handle
        repeat (5) begin        // loop 5 次 (產生+傳送)
            // `uvm_do(req);
            txn = axi_transaction::type_id::create("txn");  // 透過 factory 機制實例化 transaction
            `uvm_info("SEQ", $sformatf("Sending addr=%h, data=%h", txn.addr, txn.data), UVM_MEDIUM)     // 這裡只是印出資訊
            // start_item, randomize, finish_item
            // start_item: 對 transaction 做設定, 把 sequence_item, sequence, sequencer 連接起來
            // randomize: 隨機化 transaciton
            // finish_item: 把 sequence_item 發送出去
            start_item(txn);
            if(!txn.randomize())
                `uvm_error("", "Randomize failed")
            finish_item(txn);
        end
    endtask

endclass

// axi_driver繼承自uvm_driver，用於將AXI事務轉換為DUT訊號
class axi_driver extends uvm_driver #(axi_transaction);

    `uvm_component_utils(axi_driver)    // 透過 uvm_component_utils 向 factory 註冊該 class (uvm_component 的子類都要)

    virtual axi_if.drv vif;

    function new(string name = "axi_driver", uvm_component parent); // PS: 這裡多了一個 parent class 要傳遞, 以供環境要查找 Func 用
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi_if.drv)::get(this, "", "vif", vif))
            `uvm_fatal("DRIVER", "Virtual interface not found!")        //從 UVM 配置數據庫中找 vif，最後丟到 vif 變數中。
    endfunction

    task run_phase(uvm_phase phase);
        axi_transaction txn;
        forever begin
            seq_item_port.get_next_item(txn); // 獲得 sequence 發送的transaction
            vif.addr  = txn.addr;
            vif.data  = txn.data;
            vif.valid = 1'b1;
            wait (vif.ready);                 // 等待 DUT ready 信號
            vif.valid = 1'b0;
            seq_item_port.item_done();        // 告知 Sequencer 完成 transaction 處理
            `uvm_info("DRV", $sformatf("Sent addr=%h, data=%h", txn.addr, txn.data), UVM_MEDIUM)
        end
    endtask

endclass



// sequencer繼承uvm_seqr，用於協調driver & sequence
class axi_sequencer extends uvm_sequencer#(axi_transaction);

    `uvm_component_utils(axi_sequencer)

    function new(string name = "axi_sequencer", uvm_component parent);
        super.new(name, parent);
    endfunction

endclass



class axi_env extends uvm_env;

    `uvm_component_utils(axi_env)

    axi_driver drv;
    axi_sequecer seqr;  // **加入 sequencer**
    axi_sequence seq;

    function new(string name = "axi_env", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        drv = axi_driver::type_id::create("drv", this);
        seqr = axi_sequencer::type_id::create("seqr", this);  // **建立 sequencer**
        seq = axi_sequence::type_id::create("seq");
        drv.seq_item_port.connect(seqr.seq_item_export); //連接driver和sequencer
        // env中不需要單獨定義connect_phase，因為build phase已經完成了sequencer & //driver的連接
    endfunction

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        seq.start(seqr);  // **修正：傳入 sequencer，而不是 sequence**
        phase.drop_objection(this);
    endtask

endclass

// test
class axi_test extends uvm_test;

    `uvm_component_utils(axi_test)

    axi_env env;

    function new(string name = "axi_test", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = axi_env::type_id::create("env", this);
        
    endfunction

endclass



module top;

    bit clk;

    always #5 clk = ~clk;

    axi_if axi(clk);

    initial begin
        uvm_config_db#(virtual axi_if.drv)::set(null, "uvm_test_top.env.drv", "vif", axi);      // 在 UVM 配置數據庫設置 vif 其值為 axi interface
        run_test("axi_test");
    end

endmodule