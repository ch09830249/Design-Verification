class tlul_get_driver extends uvm_driver #(tlul_transaction);
  `uvm_component_utils(tlul_get_driver)
  virtual tlul_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual tlul_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not set for tlul_get_driver");
  endfunction

  virtual task run_phase(uvm_phase phase);
    tlul_transaction tr;
    #20;
    forever begin
      seq_item_port.get_next_item(tr);

      `uvm_info(get_type_name(), "before get", UVM_MEDIUM)
      tr.print();

      // Drive A channel
      vif.a_valid    <= 1;
      vif.a_opcode   <= tr.opcode;
      vif.a_param    <= tr.param;
      vif.a_size     <= tr.size;
      vif.a_mask     <= tr.mask;
      vif.a_address  <= tr.address;
      vif.a_data     <= tr.data;
      vif.a_source   <= tr.source;

      // 等 a_ready 代表 address 已被取走, 放下 a_valid
      @(posedge vif.clk);
      wait (vif.a_ready);
      vif.a_valid <= 0;

      // 如果是 Get，等待 Response 在 D channel
      if (tr.is_get) begin
        @(posedge vif.clk);
        wait (vif.d_valid);
        tr.resp_opcode  = vif.d_opcode;
        tr.resp_param   = vif.d_param;
        tr.resp_size    = vif.d_size;
        tr.resp_data    = vif.d_data;
        tr.resp_source  = vif.d_source;
        tr.resp_sink    = vif.d_sink;
        // Handshake response
        vif.d_ready <= 1;       // 告訴 module 我已取走 data
        @(posedge vif.clk);
        vif.d_ready <= 0;       // 下個 clk 放下 d_ready
      end
      else
        `uvm_fatal("tlul_get_driver", "Not get request!!!")

      `uvm_info(get_type_name(), "after read", UVM_MEDIUM)
      tr.print();

      seq_item_port.item_done();
    end
  endtask
endclass
