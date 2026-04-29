`ifndef APB_SLAVE_MONITOR_SV
`define APB_SLAVE_MONITOR_SV

class apb_slave_monitor extends apb_monitor_base;
    `uvm_component_utils(apb_slave_monitor)

    function new ( string name = "apb_slave_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        forever begin
            @ ( posedge vif.PCLK );
            if ( vif.PSEL && vif.PENABLE ) begin  // Access Phase
                txn = apb_seq_item :: type_id :: create ("txn");
                // Only Master Signal
                txn.PADDR   = vif.PADDR;
                txn.PWRITE  = vif.PWRITE;
                txn.PSEL    = vif.PSEL;
                txn.PENABLE = vif.PENABLE;
                txn.PWDATA  = vif.PWDATA;
                port.write(txn);  // Send txn to agt_slv_drv
            end
        end
    endtask
endclass

`endif
