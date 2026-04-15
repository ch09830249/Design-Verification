`ifndef APB_SLAVE_MONITOR_SV
`define APB_SLAVE_MONITOR_SV

class ahb_slave_monitor extends ahb_monitor_base;
    `uvm_component_utils(apb_slave_monitor)

    function new ( string name = "apb_slave_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        forever begin
            @ ( posedge vif.PCLK );
            if ( vif.PSEL && !vif.PENABLE ) begin  // Setup Phase
                txn = apb_seq_item :: type_id :: create ("txn");
                txn.PADDR   = vif.PADDR;
                txn.PWRITE  = vif.PWRITE;
                txn.PSEL    = vif.PSEL;
                txn.PWDATA  = vif.PWDATA;
                txn.PENABLE = vif.PENABLE;
                port.write(txn);
            end
        end
    endtask
endclass

`endif
