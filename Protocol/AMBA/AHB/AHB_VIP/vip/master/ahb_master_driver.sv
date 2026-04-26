`ifndef AHB_MASTER_DRIVER_SV
`define AHB_MASTER_DRIVER_SV

class ahb_master_driver extends ahb_driver_base;
    `uvm_component_utils(ahb_master_driver)

    ahb_seq_item    addr_txn_queue[$];
    ahb_seq_item    data_txn_queue[$];

    function new ( string name = "ahb_master_driver", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        reset_signal();
        fork
            insert_cmd_queue();
            addr_txn_drive();
            data_txn_drive();
        join
    endtask

    task insert_cmd_queue();
        forever begin
            seq_item_port.get_next_item(txn);
            case ( txn.HBURST )
                `HBURST_SINGLE: begin
                    addr_txn_queue.push_back(txn);
                end
                `HBURST_INCR:   begin
                    bit [`D_ADDR_WIDTH-1:0] cur_addr;
                    // burst transfer - first beat
                    addr_txn_queue.push_back(txn);
                    
                    // burst transfer - following beats
                    cur_addr  = txn.HADDR;
                    for ( int i = 1; i < txn.burst_len; i++ ) begin
                        ahb_seq_item new_txn;
                        $cast(new_txn, txn.clone());
                        cur_addr        = cur_addr + (1 << txn.HSIZE);
                        new_txn.HADDR   = cur_addr;
                        new_txn.HTRANS  = `HTRANS_SEQ;
                        addr_txn_queue.push_back(new_txn);
                    end
                end
                default: begin
                    `uvm_error("MSTDRV", $sformatf("Unsupported HBURST: %0h", txn.HBURST))
                end
            endcase
            seq_item_port.item_done();
        end
    endtask

    task addr_txn_drive();
        ahb_seq_item                cur_txn;
        forever begin
            @( posedge vif.HCLK );
            if ( !vif.HRESETn ) begin
                reset_signal();
            end else begin
                if ( addr_txn_queue.size() > 0  && vif.HREADY) begin    // Drive the next txn until HREADY == 1
                    // Drive Master Signals
                    cur_txn         = addr_txn_queue.pop_front();
                    vif.HSEL        <= cur_txn.HSEL;
                    vif.HADDR       <= cur_txn.HADDR;
                    vif.HWRITE      <= cur_txn.HWRITE;
                    vif.HSIZE       <= cur_txn.HSIZE;
                    vif.HBURST      <= cur_txn.HBURST;
                    vif.HTRANS      <= cur_txn.HTRANS;
                    vif.HPROT       <= cur_txn.HPROT;
                    vif.HMASTLOCK   <= cur_txn.HMASTLOCK;
                    if ( cur_txn.HWRITE ) begin
                        data_txn_queue.push_back(cur_txn);
                    end
                end else if ( addr_txn_queue.size() == 0 && data_txn_queue.size() == 0 && vif.HREADY ) begin    // All txns finished
                    reset_signal();
                end
            end
        end
    endtask

    task data_txn_drive();
        ahb_seq_item                cur_txn;
        logic [`D_DATA_WIDTH-1:0]   pending_HWDATA;
        bit                         has_pending;

        has_pending = 0;
        forever begin
            @( posedge vif.HCLK );
            if ( !vif.HRESETn ) begin
                reset_signal();
            end else begin
                if ( vif.HREADY ) begin
                    // Drive the previous txn data
                    if ( has_pending ) begin
                        vif.HWDATA  <= pending_HWDATA;
                        has_pending  = 0;
                    end else begin      // No previous txn
                        vif.HWDATA <= '0;
                    end
                    // Record the current txn and drive at the next clk
                    if ( data_txn_queue.size() > 0 ) begin
                        cur_txn        = data_txn_queue.pop_front();
                        pending_HWDATA = cur_txn.HWDATA;
                        has_pending    = 1;
                    end
                end
            end
        end
    endtask

    task reset_signal();
        vif.HSEL        <= '0;
        vif.HADDR       <= '0;
        vif.HWRITE      <= '0;
        vif.HSIZE       <= '0;
        vif.HBURST      <= '0;
        vif.HPROT       <= '0;
        vif.HMASTLOCK   <= '0;
        vif.HTRANS      <= `HTRANS_IDLE;
        vif.HWDATA      <= '0;
    endtask

endclass

`endif
