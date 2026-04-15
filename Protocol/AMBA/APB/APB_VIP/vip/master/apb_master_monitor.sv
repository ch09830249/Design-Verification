`ifndef APB_MASTER_MONITOR_SV
`define APB_MASTER_MONITOR_SV

class apb_master_monitor extends apb_monitor_base;
    `uvm_component_utils(apb_master_monitor)

    function new ( string name = "apb_master_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        forever begin
            @ ( posedge vif.PCLK );
            if ( vif.PSEL ) begin  // Write whenever PSEL != 0
                txn = apb_seq_item :: type_id :: create ("txn");
                txn.PADDR   = vif.PADDR;
                txn.PWRITE  = vif.PWRITE;
                txn.PSEL    = vif.PSEL;
                txn.PWDATA  = vif.PWDATA;
                txn.PRDATA  = vif.PRDATA;
                txn.PENABLE = vif.PENABLE;
                port.write(txn);
            end
        end
    endtask
endclass

`endif
