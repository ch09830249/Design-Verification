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
            if ( vif.PSEL && vif.PENABLE && vif.PREADY ) begin  // Access phase complete
                txn = apb_seq_item :: type_id :: create ("txn");
                // Master Signal
                txn.PADDR   = vif.PADDR;
                txn.PWRITE  = vif.PWRITE;
                txn.PSEL    = vif.PSEL;
                txn.PENABLE = vif.PENABLE;
                txn.PWDATA  = vif.PWDATA;
                // Slave Signal
                txn.PREADY  = vif.PREADY;
                txn.PRDATA  = vif.PRDATA;
                txn.PSLVERR = vif.PSLVERR;
                port.write(txn);  // Send txn to scb and cov
            end
        end
    endtask
endclass

`endif
