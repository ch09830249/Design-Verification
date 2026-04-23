`ifndef AHB_MASTER_MONITOR_SV
`define AHB_MASTER_MONITOR_SV

class ahb_master_monitor extends ahb_monitor_base;
    `uvm_component_utils(ahb_master_monitor)

    ahb_seq_item    addr_phase_txn;

    function new ( string name = "ahb_master_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        // 等 reset 結束才開始採樣
        wait ( !vif.HRESETn );
        wait ( vif.HRESETn );

        forever begin
            @( posedge vif.HCLK );

            if ( !vif.HRESETn ) begin
                // Reset 期間清掉暫存
                addr_phase_txn = null;
            end else if ( vif.HREADY ) begin

                // ----------------------------------------
                // Data Phase — 處理上一個 address phase
                // ----------------------------------------
                if ( addr_phase_txn != null ) begin
                    txn = ahb_seq_item :: type_id :: create ("txn");

                    // Address phase 資訊從 addr_phase_txn 取得
                    txn.HADDR       = addr_phase_txn.HADDR;
                    txn.HBURST      = addr_phase_txn.HBURST;
                    txn.HMASTLOCK   = addr_phase_txn.HMASTLOCK;
                    txn.HPROT       = addr_phase_txn.HPROT;
                    txn.HSIZE       = addr_phase_txn.HSIZE;
                    txn.HTRANS      = addr_phase_txn.HTRANS;
                    txn.HWRITE      = addr_phase_txn.HWRITE;
                    txn.HSEL        = addr_phase_txn.HSEL;

                    // Data phase 資訊從 vif 直接採樣
                    txn.HRDATA  = vif.HRDATA;
                    txn.HREADY  = vif.HREADY;
                    txn.HRESP   = vif.HRESP;
                    if ( addr_phase_txn.HWRITE ) begin
                        txn.HWDATA = vif.HWDATA;
                    end else begin
                        txn.HWDATA = '0;
                    end
                    port.write(txn);
                    addr_phase_txn = null;
                end

                // ----------------------------------------
                // Address Phase — 採樣當前 address phase
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
