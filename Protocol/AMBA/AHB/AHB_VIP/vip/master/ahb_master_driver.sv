`ifndef AHB_MASTER_DRIVER_SV
`define AHB_MASTER_DRIVER_SV

class ahb_master_driver extends ahb_driver_base;
    `uvm_component_utils(ahb_master_driver)

    function new ( string name = "ahb_master_driver", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        reset_signal();
        forever begin
            @( posedge vif.HCLK );
            if ( !vif.HRESETn ) begin
                reset_signal();
            end else begin
                seq_item_port.get_next_item(txn);

                case ( txn.HBURST )
                    `HBURST_SINGLE: do_single();
                    `HBURST_INCR:   do_incr();
                    default: begin
                        `uvm_error("MSTDRV", $sformatf("Unsupported HBURST: %0h", txn.HBURST))
                    end
                endcase

                seq_item_port.item_done();
            end
        end
    endtask

    // -------------------------------------------------------
    // SINGLE transfer
    // -------------------------------------------------------
    task do_single();
        // Clock N — Address Phase
        vif.HSEL    <= txn.HSEL;
        vif.HADDR   <= txn.HADDR;
        vif.HWRITE  <= txn.HWRITE;
        vif.HSIZE   <= txn.HSIZE;
        vif.HBURST  <= `HBURST_SINGLE;
        vif.HTRANS  <= `HTRANS_NONSEQ;
        vif.HWDATA  <= '0;

        // Clock N+1 — Data Phase
        // 等 HREADY，slave 可能插入 wait state
        @( posedge vif.HCLK );
        while ( !vif.HREADY ) @( posedge vif.HCLK );

        // Data Phase：送出資料，同時送 IDLE 給下一筆
        vif.HWDATA  <= txn.HWDATA;
        vif.HTRANS  <= `HTRANS_IDLE;
        vif.HSEL    <= '0;

        // 等最後一筆 data phase 完成
        @( posedge vif.HCLK );
        while ( !vif.HREADY ) @( posedge vif.HCLK );

        reset_signal();
    endtask

    // -------------------------------------------------------
    // INCR burst — pipeline 版本
    // -------------------------------------------------------
    task do_incr();
        bit [`D_ADDR_WIDTH-1:0] cur_addr;
        int unsigned            byte_size;

        cur_addr  = txn.HADDR;
        byte_size = (1 << txn.HSIZE);

        // Clock 1 — 第一筆 Address Phase
        vif.HSEL    <= txn.HSEL;
        vif.HADDR   <= cur_addr;
        vif.HWRITE  <= txn.HWRITE;
        vif.HSIZE   <= txn.HSIZE;
        vif.HBURST  <= `HBURST_INCR;
        vif.HTRANS  <= `HTRANS_NONSEQ;
        vif.HWDATA  <= '0;

        // Clock 2 ~ N — Pipeline：Data Phase[i] 和 Address Phase[i+1] 同時進行
        for ( int i = 1; i < txn.burst_len; i++ ) begin
            @( posedge vif.HCLK );
            while ( !vif.HREADY ) @( posedge vif.HCLK );

            // Data Phase[i-1] 和 Address Phase[i] 同時
            cur_addr    =  cur_addr + byte_size;
            vif.HADDR   <= cur_addr;
            vif.HTRANS  <= `HTRANS_SEQ;
            vif.HWDATA  <= txn.HWDATA;  // 上一筆的 data
        end

        // 最後一筆 Data Phase — 送完資料，同時拉 IDLE
        @( posedge vif.HCLK );
        while ( !vif.HREADY ) @( posedge vif.HCLK );

        vif.HWDATA  <= txn.HWDATA;
        vif.HTRANS  <= `HTRANS_IDLE;
        vif.HSEL    <= '0;

        // 等最後一筆 data phase 完成
        @( posedge vif.HCLK );
        while ( !vif.HREADY ) @( posedge vif.HCLK );

        reset_signal();
    endtask

    task reset_signal();
        vif.HSEL    <= '0;
        vif.HADDR   <= '0;
        vif.HWRITE  <= '0;
        vif.HSIZE   <= '0;
        vif.HBURST  <= '0;
        vif.HTRANS  <= `HTRANS_IDLE;
        vif.HWDATA  <= '0;
    endtask

endclass

`endif
