`ifndef AHB_SLAVE_MONITOR_SV
`define AHB_SLAVE_MONITOR_SV

class ahb_slave_monitor extends ahb_monitor_base;
    `uvm_component_utils(ahb_slave_monitor)

    function new ( string name = "ahb_slave_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        wait ( !vif.HRESETn );
        wait ( vif.HRESETn );
        forever begin
            @( posedge vif.HCLK );
            if ( vif.HRESETn ) begin
                if ( vif.HREADY && vif.HSEL &&
                ( vif.HTRANS == `HTRANS_NONSEQ || vif.HTRANS == `HTRANS_SEQ    )) begin  // Address Phase
                    txn = ahb_seq_item :: type_id :: create ("txn");
                    txn.HADDR   = vif.HADDR;
                    txn.HWRITE  = vif.HWRITE;
                    txn.HSIZE   = vif.HSIZE;
                    txn.HBURST  = vif.HBURST;
                    txn.HTRANS  = vif.HTRANS;
                    txn.HSEL    = vif.HSEL;
                    txn.HWDATA  = vif.HWDATA;  // 下一拍才有效，這裡先採樣
                    port.write(txn);
                end
            end
        end
    endtask

endclass

`endif
