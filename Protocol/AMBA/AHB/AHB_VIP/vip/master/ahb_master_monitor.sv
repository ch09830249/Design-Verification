`ifndef AHB_MASTER_MONITOR_SV
`define AHB_MASTER_MONITOR_SV

class ahb_master_monitor extends ahb_monitor_base;
    `uvm_component_utils(ahb_master_monitor)

    ahb_seq_item    addr_phase_txn; // previous pending txn

    function new ( string name = "ahb_master_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        wait ( !vif.HRESETn );
        wait ( vif.HRESETn );

        forever begin
            @( posedge vif.HCLK );

            if ( !vif.HRESETn ) begin
                // Clear previous pending txn
                addr_phase_txn = null;
            end else if ( vif.HREADY ) begin
                // ----------------------------------------
                // Data Phase — handle the previous pending txn
                // ----------------------------------------
                if ( addr_phase_txn != null ) begin
                    txn = ahb_seq_item :: type_id :: create ("txn");

                    // Get infos of Address phase from addr_phase_txn
                    txn.HADDR       = addr_phase_txn.HADDR;
                    txn.HBURST      = addr_phase_txn.HBURST;
                    txn.HMASTLOCK   = addr_phase_txn.HMASTLOCK;
                    txn.HPROT       = addr_phase_txn.HPROT;
                    txn.HSIZE       = addr_phase_txn.HSIZE;
                    txn.HTRANS      = addr_phase_txn.HTRANS;
                    txn.HWRITE      = addr_phase_txn.HWRITE;
                    txn.HSEL        = addr_phase_txn.HSEL;

                    // Get infos of Data phase by sampling vif signals
                    txn.HRDATA  = vif.HRDATA;
                    txn.HREADY  = vif.HREADY;
                    txn.HRESP   = vif.HRESP;
                    if ( addr_phase_txn.HWRITE ) begin
                        txn.HWDATA = vif.HWDATA;
                    end else begin
                        txn.HWDATA = '0;
                    end
                    port.write(txn);    // Sending txn to scb and coverage
                    addr_phase_txn = null;
                end

                // ----------------------------------------
                // Address Phase — Sample signals of address phase
                // ----------------------------------------
                if ( vif.HTRANS == `HTRANS_IDLE ) begin
                    addr_phase_txn = null;
                end else if ( vif.HSEL && ( vif.HTRANS == `HTRANS_NONSEQ || vif.HTRANS == `HTRANS_SEQ )) begin
                    addr_phase_txn = ahb_seq_item :: type_id :: create ("addr_phase_txn");
                    addr_phase_txn.HADDR        = vif.HADDR;
                    addr_phase_txn.HBURST       = vif.HBURST;
                    addr_phase_txn.HMASTLOCK    = vif.HMASTLOCK;
                    addr_phase_txn.HPROT        = vif.HPROT;
                    addr_phase_txn.HSIZE        = vif.HSIZE;
                    addr_phase_txn.HTRANS       = vif.HTRANS;
                    addr_phase_txn.HWRITE       = vif.HWRITE;
                    addr_phase_txn.HSEL         = vif.HSEL;
                end
            end
        end
    endtask
endclass

`endif
