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
                vif.PREADY  <= 1;
                vif.PRDATA  <= 0;
                vif.PSLVERR <= 0;
            end else begin
                if ( vif.PSEL && vif.PENABLE ) begin  // Access Phase
                    vif.PREADY  <= 1;
                    vif.PSLVERR <= 0;  // this slave never generates error
                    if ( vif.PWRITE ) begin
                        mem[vif.PADDR[$clog2(`D_MEM_SIZE)-1:0]] <= vif.PWDATA;
                    end else begin
                        vif.PRDATA = mem[vif.PADDR[$clog2(`D_MEM_SIZE)-1:0]];
                    end
                end
            end
        end
    endtask
endclass

`endif
