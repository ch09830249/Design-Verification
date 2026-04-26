`ifndef AHB_SLAVE_MONITOR_SV
`define AHB_SLAVE_MONITOR_SV

class ahb_slave_monitor extends ahb_monitor_base;
    `uvm_component_utils(ahb_slave_monitor)

    function new ( string name = "ahb_slave_monitor", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        // 用來暫存 Address Phase 資訊
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
                addr_phase_valid = 0;  // Reset 時清除暫存
            end
            else begin

                // ────────────────────────────────────────
                // Data Phase：上一拍儲存的 Address + 這拍的 HWDATA
                // ────────────────────────────────────────
                if ( addr_phase_valid && vif.HREADY ) begin
                    txn = ahb_seq_item::type_id::create("txn");
                    txn.HADDR  = saved_haddr;
                    txn.HWRITE = saved_hwrite;
                    txn.HSIZE  = saved_hsize;
                    txn.HBURST = saved_hburst;
                    txn.HTRANS = saved_htrans;
                    txn.HSEL   = saved_hsel;
                    txn.HWDATA = (saved_hwrite)  ? vif.HWDATA : '0; // WRITE 才有 HWDATA
                    txn.HRDATA = (!saved_hwrite) ? vif.HRDATA : '0;
                    txn.HRESP  = vif.HRESP;
                    port.write(txn);        // Send to fifo
                    addr_phase_valid = 0;
                end

                // ────────────────────────────────────────
                // Address Phase：只儲存，不送出
                // ────────────────────────────────────────
                if ( vif.HREADY && vif.HSEL &&
                   ( vif.HTRANS == `HTRANS_NONSEQ || vif.HTRANS == `HTRANS_SEQ )) begin
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
