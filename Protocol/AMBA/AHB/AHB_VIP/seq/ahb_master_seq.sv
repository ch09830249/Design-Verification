`ifndef AHB_MASTER_SEQ_SV
`define AHB_MASTER_SEQ_SV

class ahb_master_seq extends uvm_sequence #(ahb_seq_item);
    `uvm_object_utils(ahb_master_seq)

    ahb_seq_item        txn;

    function new ( string name = "ahb_master_seq" );
        super.new(name);
    endfunction

    virtual task body();
        for ( int i = 0; i < MASTER_TXN_NUM; i += 1 ) begin
            txn = ahb_seq_item :: type_id :: create ("txn");

            if ( !txn.randomize() )
                `uvm_fatal("RANDERR", "txn randomize fail!")

            start_item(txn);
            finish_item(txn);
        end
    endtask

endclass

`endif
