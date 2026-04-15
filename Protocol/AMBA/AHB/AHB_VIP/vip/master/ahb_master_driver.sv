`ifndef APB_MASTER_DRIVER_SV
`define APB_MASTER_DRIVER_SV

class ahb_master_driver extends ahb_driver_base;
    `uvm_component_utils(apb_master_driver)

    function new ( string name = "apb_master_driver", uvm_component parent );
        super.new(name, parent);
    endfunction

    virtual task run_phase ( uvm_phase phase );
        forever begin
            @ ( posedge vif.PCLK );
            if ( !vif.PRESETn ) begin
                reset_signal();
            end else begin
                txn = apb_seq_item :: type_id :: create ("txn");

                seq_item_port.get_next_item(txn);

                if ( txn.PWRITE ) begin  // APB write
                    @ ( posedge vif.PCLK );
                    vif.PADDR   <= txn.PADDR;
                    vif.PSEL    <= txn.PSEL;
                    vif.PWDATA  <= txn.PWDATA;
                    vif.PWRITE  <= 1;

                    @ ( posedge vif.PCLK );
                    vif.PENABLE <= 1;

                    @ ( posedge vif.PCLK );
                    wait ( vif.PREADY );
                    reset_signal();
                    
                end else begin  // APB read
                    @ ( posedge vif.PCLK );
                    vif.PADDR   <= txn.PADDR;
                    vif.PSEL    <= txn.PSEL;
                    vif.PWRITE  <= 0;

                    @ ( posedge vif.PCLK );
                    vif.PENABLE <= 1;

                    @ ( posedge vif.PCLK );
                    wait ( vif.PREADY );
                    reset_signal();
                end

                seq_item_port.item_done();
            end
        end
    endtask

    task reset_signal();
        vif.PADDR   <= '0;
        vif.PWRITE  <= '0;
        vif.PSEL    <= '0;
        vif.PENABLE <= '0;
        vif.PWDATA  <= '0;
    endtask
endclass

`endif
