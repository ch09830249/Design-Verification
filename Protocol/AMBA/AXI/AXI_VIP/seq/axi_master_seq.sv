`ifndef AXI_MASTER_SEQ_SV
`define AXI_MASTER_SEQ_SV

class axi_master_seq extends uvm_sequence #(axi_seq_item);
    `uvm_object_utils(axi_master_seq)

    axi_seq_item    txn;

    function new(string name = "axi_master_seq");
        super.new(name);
    endfunction

    virtual task body();
        for (int i = 0; i < 3000; i++) begin
            txn = axi_seq_item::type_id::create("txn");

            if (!txn.randomize())
                `uvm_fatal("RANDERR", "txn randomize fail!")

            start_item(txn);
            finish_item(txn);
        end
    endtask

endclass

`endif
