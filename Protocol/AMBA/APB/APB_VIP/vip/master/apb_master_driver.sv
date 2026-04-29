`ifndef APB_MASTER_DRIVER_SV
`define APB_MASTER_DRIVER_SV

class apb_master_driver extends apb_driver_base;
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
                seq_item_port.get_next_item(txn);

                // Setup Phase
                vif.PADDR   <= txn.PADDR;
                vif.PWRITE  <= txn.PWRITE;
                vif.PSEL    <= txn.PSEL;
                vif.PWDATA  <= txn.PWDATA;
                vif.PENABLE <= 0;

                // Access Phase
                @ ( posedge vif.PCLK );
                vif.PENABLE <= 1;

                // Wait PREADY：必須在 PENABLE=1 之後的 posedge 才檢查
                do begin
                    @ ( posedge vif.PCLK );
                end while ( !vif.PREADY );  // ← posedge 上檢查，不夠再等下一拍

                // PREADY=1 的那個 posedge 結束後才 reset
                reset_signal();

                seq_item_port.item_done();
            end
        end
    endtask

    task reset_signal();
        vif.PADDR   <= '0;
        vif.PWRITE  <= '0;
        vif.PSEL    <= '0;
        vif.PWDATA  <= '0;
        vif.PENABLE <= '0;
    endtask
endclass

`endif
