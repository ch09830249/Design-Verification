`ifndef APB_SLAVE_DRIVER_SV
`define APB_SLAVE_DRIVER_SV

class apb_slave_driver extends apb_driver_base;
    `uvm_component_utils(apb_slave_driver)

    logic [`D_DATA_WIDTH-1:0]       mem [`D_MEM_SIZE-1:0];

    function new ( string name = "apb_slave_driver", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);
        foreach ( mem[i] )  mem[i] = 0;
    endfunction

    virtual task run_phase ( uvm_phase phase );
        forever begin
            @ ( posedge vif.PCLK );
            if ( !vif.PRESETn ) begin
                vif.PRDATA  <= 0;
                vif.PREADY  <= 1;
            end else begin
                seq_item_port.get_next_item(txn);
                if ( txn.PSEL && txn.PENABLE ) begin  // Setup Phase
                    vif.PREADY  <= 0;
                    #1;  // simulate delay
                    vif.PREADY  <= 1;
                    vif.PSLVERR <= txn.PSLVERR;
                    if ( txn.PWRITE ) begin
                        mem[txn.PADDR[$clog2(`D_MEM_SIZE)-1:0]] <= txn.PWDATA;
                    end else begin
                        vif.PRDATA <= mem[txn.PADDR[$clog2(`D_MEM_SIZE)-1:0]];
                    end
                end
                seq_item_port.item_done();
            end
        end
    endtask
endclass

`endif
