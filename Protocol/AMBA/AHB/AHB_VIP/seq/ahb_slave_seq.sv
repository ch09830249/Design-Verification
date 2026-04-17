`ifndef AHB_SLAVE_SEQ_SV
`define AHB_SLAVE_SEQ_SV

class ahb_slave_seq extends uvm_sequence;
    `uvm_object_utils(ahb_slave_seq)

    ahb_seq_item                            txn;
    uvm_tlm_analysis_fifo #(ahb_seq_item)   fifo;

    function new ( string name = "ahb_slave_seq" );
        super.new(name);
    endfunction

    virtual task pre_start();
        if ( !uvm_config_db #(uvm_tlm_analysis_fifo #(ahb_seq_item)) :: get (null, get_full_name(), "fifo", fifo) )
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
