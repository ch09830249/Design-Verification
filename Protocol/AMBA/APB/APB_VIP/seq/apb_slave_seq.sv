`ifndef APB_SLAVE_SEQ_SV
`define APB_SLAVE_SEQ_SV

class apb_slave_seq extends uvm_sequence;
    `uvm_object_utils(apb_slave_seq)

    apb_seq_item                            txn;
    uvm_tlm_analysis_fifo #(apb_seq_item)   fifo;

    function new ( string name = "apb_slave_seq" );
        super.new(name);
    endfunction

    virtual task pre_start();
        if ( !uvm_config_db #(uvm_tlm_analysis_fifo #(apb_seq_item)) :: get (null, get_full_name(), "fifo", fifo) )
            `uvm_fatal("NOFIFO", $sformatf("No fifo set for %s.fifo", get_full_name() ))
    endtask

    virtual task body();
        forever begin
            fifo.get(txn);
            start_item(txn);
            finish_item(txn);
        end
    endtask
endclass

`endif
