`ifndef AHB_SLAVE_MONITOR_SV
`define AHB_SLAVE_MONITOR_SV

class ahb_slave_monitor extends ahb_monitor_base;
    `uvm_component_utils(ahb_slave_monitor)

    function new ( string name = "ahb_slave_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        // Save the signals of address Phase
        logic        saved_hwrite;
        logic [63:0] saved_haddr;
        logic [2:0]  saved_hsize;
        logic [2:0]  saved_hburst;
        logic [1:0]  saved_htrans;
        logic        saved_hsel;
        logic        addr_phase_valid;

        addr_phase_valid = 0;

        wait ( !vif.HRESETn );
        wait ( vif.HRESETn );

        forever begin
            @( posedge vif.HCLK );

            if ( !vif.HRESETn ) begin
                addr_phase_valid = 0;  // Reset the saved signals
            end
            else begin
                // ────────────────────────────────────────
                // Data Phase：Create txn, sample HRESP and just print all the fields of txn
                // ────────────────────────────────────────
                if ( addr_phase_valid && vif.HREADY ) begin
                    txn = ahb_seq_item::type_id::create("txn");
                    txn.HADDR  = saved_haddr;
                    txn.HWRITE = saved_hwrite;
                    txn.HSIZE  = saved_hsize;
                    txn.HBURST = saved_hburst;
                    txn.HTRANS = saved_htrans;
                    txn.HSEL   = saved_hsel;
                    txn.HWDATA = (saved_hwrite)  ? vif.HWDATA : '0;
                    txn.HRDATA = (!saved_hwrite) ? vif.HRDATA : '0;
                    txn.HRESP  = vif.HRESP;
                    // txn.print();
                    addr_phase_valid = 0;
                end

                // ────────────────────────────────────────
                // Address Phase：Save the signals of address phase
                // ────────────────────────────────────────
                if ( vif.HREADY && vif.HSEL && ( vif.HTRANS == `HTRANS_NONSEQ || vif.HTRANS == `HTRANS_SEQ )) begin
                    saved_haddr  = vif.HADDR;
                    saved_hwrite = vif.HWRITE;
                    saved_hsize  = vif.HSIZE;
                    saved_hburst = vif.HBURST;
                    saved_htrans = vif.HTRANS;
                    saved_hsel   = vif.HSEL;
                    addr_phase_valid = 1;
                end
            end
        end
    endtask
endclass

`endif
