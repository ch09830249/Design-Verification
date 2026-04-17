`ifndef AHB_MASTER_MONITOR_SV
`define AHB_MASTER_MONITOR_SV

class ahb_master_monitor extends ahb_monitor_base;
    `uvm_component_utils(ahb_master_monitor)

    // 暫存 address phase 資訊
    ahb_seq_item    addr_phase_txn;

    function new ( string name = "ahb_master_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        forever begin
            @( posedge vif.HCLK );

            if ( vif.HREADY ) begin

                // ----------------------------------------
                // Data Phase — 處理上一個 address phase
                // ----------------------------------------
                if ( addr_phase_txn != null ) begin
                    txn = ahb_seq_item :: type_id :: create ("txn");

                    // Address phase 資訊（上一拍採樣的）
                    txn.HADDR   = addr_phase_txn.HADDR;
                    txn.HWRITE  = addr_phase_txn.HWRITE;
                    txn.HSIZE   = addr_phase_txn.HSIZE;
                    txn.HBURST  = addr_phase_txn.HBURST;
                    txn.HTRANS  = addr_phase_txn.HTRANS;
                    txn.HSEL    = addr_phase_txn.HSEL;

                    // Data phase 資訊（這一拍採樣的）
                    txn.HWDATA  = vif.HWDATA;
                    txn.HRDATA  = vif.HRDATA;
                    txn.HRESP   = vif.HRESP;
                    txn.HREADY  = vif.HREADY;

                    port.write(txn);
                    addr_phase_txn = null;
                end

                // ----------------------------------------
                // Address Phase — 採樣當前 address phase
                // ----------------------------------------
                if ( vif.HSEL && ( vif.HTRANS == `HTRANS_NONSEQ ||
                                   vif.HTRANS == `HTRANS_SEQ    )) begin
                    addr_phase_txn = ahb_seq_item :: type_id :: create ("addr_phase_txn");
                    addr_phase_txn.HADDR  = vif.HADDR;
                    addr_phase_txn.HWRITE = vif.HWRITE;
                    addr_phase_txn.HSIZE  = vif.HSIZE;
                    addr_phase_txn.HBURST = vif.HBURST;
                    addr_phase_txn.HTRANS = vif.HTRANS;
                    addr_phase_txn.HSEL   = vif.HSEL;
                end

            end
        end
    endtask

endclass

`endif
