`ifndef AHB_SLAVE_DRIVER_SV
`define AHB_SLAVE_DRIVER_SV

class ahb_slave_driver extends ahb_driver_base;
    `uvm_component_utils(ahb_slave_driver)

    logic [`D_DATA_WIDTH-1:0]   mem [`D_MEM_SIZE-1:0];

    logic [`D_ADDR_WIDTH-1:0]   addr_reg;
    logic                       write_reg;
    logic [2:0]                 size_reg;
    logic                       valid_reg;

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
                seq_item_port.get_next_item(txn);

                // ----------------------------------------
                // Data Phase
                // ----------------------------------------
                if ( valid_reg ) begin
                    vif.HREADY  <= 1;
                    vif.HRESP   <= `HRESP_OKAY;

                    if ( write_reg ) begin  // Write
                        case ( size_reg )
                            `HSIZE_BYTE     : begin
                                int byte_offset = addr_reg[1:0] * 8;
                                mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]] =
                                    ( mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]] & ~(32'hFF << byte_offset) ) | ( {24'b0, vif.HWDATA[7:0]} << byte_offset );
                            end
                            `HSIZE_HALFWORD : begin
                                int byte_offset = addr_reg[1] * 16;
                                mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]] =
                                    ( mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]] & ~(32'hFFFF << byte_offset) ) | ( {16'b0, vif.HWDATA[15:0]} << byte_offset );
                            end
                            `HSIZE_WORD     : begin
                                mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]] = vif.HWDATA;
                            end
                            default         : begin
                                `uvm_error("SLVDRV", $sformatf("Unsupported HSIZE: %0h", size_reg))
                            end
                        endcase
                    end else begin          // Read
                        case ( size_reg )
                            `HSIZE_BYTE     : begin
                                int byte_offset = addr_reg[1:0] * 8;
                                vif.HRDATA <= { '0, mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]][byte_offset +: 8] };
                            end
                            `HSIZE_HALFWORD : begin
                                int byte_offset = addr_reg[1] * 16;
                                vif.HRDATA <= { '0, mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]][byte_offset +: 16] };
                            end
                            `HSIZE_WORD    : begin
                                vif.HRDATA <= mem[addr_reg[$clog2(`D_MEM_SIZE)-1:0]];
                            end
                            default        : begin
                                `uvm_error("SLVDRV", $sformatf("Unsupported HSIZE: %0h", size_reg))
                            end
                        endcase
                    end
                end

                // ----------------------------------------
                // Address Phase
                // ----------------------------------------
                if ( txn.HSEL && ( txn.HTRANS == `HTRANS_NONSEQ ||
                                   txn.HTRANS == `HTRANS_SEQ    )) begin
                    addr_reg  = txn.HADDR;
                    write_reg = txn.HWRITE;
                    size_reg  = txn.HSIZE;
                    valid_reg = 1;
                    vif.HREADY <= 1;
                end else if ( txn.HTRANS == `HTRANS_IDLE ) begin
                    valid_reg = 0;
                end

                seq_item_port.item_done();
            end
        end
    endtask

endclass

`endif
