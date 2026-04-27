`ifndef AHB_SLAVE_DRIVER_SV
`define AHB_SLAVE_DRIVER_SV

class ahb_slave_driver extends ahb_driver_base;
    `uvm_component_utils(ahb_slave_driver)

    logic [`D_DATA_WIDTH-1:0]   mem [`D_MEM_SIZE-1:0];
    logic [`D_ADDR_WIDTH-1:0]   addr_reg;
    logic                       write_reg;
    logic [2:0]                 size_reg;
    logic                       valid_reg;

    int unsigned                word_idx;
    int                         byte_offset;

    function new ( string name = "ahb_slave_driver", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);
        foreach ( mem[i] ) mem[i] = 0;
    endfunction

    virtual task run_phase ( uvm_phase phase );
        valid_reg = 0;
        forever begin
            @( posedge vif.HCLK );
            if ( !vif.HRESETn ) begin
                vif.HRDATA  <= 0;
                vif.HRESP   <= `HRESP_OKAY;
                vif.HREADY  <= 1;
                valid_reg    = 0;
            end else begin
                // ----------------------------------------
                // Data Phase
                // ----------------------------------------
                if ( valid_reg && vif.HREADY ) begin
                    // AHB write always HRESP_OKAY
                    vif.HREADY  <= 1;
                    vif.HRESP   <= `HRESP_OKAY;
                    // AHB write
                    if ( write_reg ) begin
                        word_idx = addr_reg >> $clog2(`D_DATA_WIDTH/8);  // addr_reg: addr of the previous txn
                        // $display("SLAVE WRITE: HADDR=%0h, index=%0d, HWDATA=%0h",
                        //             addr_reg,
                        //             addr_reg >> $clog2(`D_DATA_WIDTH/8),
                        //             vif.HWDATA);
                        // mask + OR
                        case ( size_reg )
                            `HSIZE_BYTE     : begin
                                byte_offset = addr_reg[1:0] * 8;
                                mem[word_idx][byte_offset +: 8] = vif.HWDATA[byte_offset +: 8];
                            end
                            `HSIZE_HALFWORD : begin
                                byte_offset = addr_reg[1] * 16;
                                mem[word_idx][byte_offset +: 16] = vif.HWDATA[byte_offset +: 16];
                            end
                            `HSIZE_WORD     : begin
                                mem[word_idx] = vif.HWDATA;
                            end
                            default         : begin
                                `uvm_error("SLVDRV", $sformatf("Unsupported HSIZE: %0h", size_reg))
                            end
                        endcase
                    end
                    valid_reg = 0;  // The previous txn finishes
                end

                // ----------------------------------------
                // Address Phase
                // ----------------------------------------
                if ( vif.HREADY && vif.HSEL && ( vif.HTRANS == `HTRANS_NONSEQ || vif.HTRANS == `HTRANS_SEQ )) begin
                    addr_reg    =   vif.HADDR;
                    write_reg   =   vif.HWRITE;
                    size_reg    =   vif.HSIZE;
                    valid_reg   =   1;
                    // zero wait state: HRDATA in the same cycle as the address phase
                    vif.HREADY  <=  1;
                    // AHB read
                    if ( !vif.HWRITE ) begin
                        word_idx = vif.HADDR >> $clog2(`D_DATA_WIDTH/8);
                        // $display("SLAVE READ: HADDR=%0h, mem[%0d]=%0h", 
                        //             vif.HADDR,
                        //             vif.HADDR >> $clog2(`D_DATA_WIDTH/8),
                        //             mem[word_idx]);
                        case ( vif.HSIZE )
                            `HSIZE_BYTE : begin
                                byte_offset = vif.HADDR[1:0] * 8;
                                vif.HRDATA <= { '0, mem[word_idx][byte_offset +: 8] };
                            end
                            `HSIZE_HALFWORD : begin
                                byte_offset = vif.HADDR[1] * 16;
                                vif.HRDATA <= { '0, mem[word_idx][byte_offset +: 16] };
                            end
                            `HSIZE_WORD : begin
                                vif.HRDATA <= mem[word_idx];
                            end
                            default : begin
                                `uvm_error("SLVDRV", $sformatf("Unsupported HSIZE: %0h", vif.HSIZE))
                            end
                        endcase
                    end
                end else if ( vif.HTRANS == `HTRANS_IDLE || vif.HTRANS == `HTRANS_BUSY ) begin
                    valid_reg = 0;
                end
            end
        end
    endtask
endclass

`endif
