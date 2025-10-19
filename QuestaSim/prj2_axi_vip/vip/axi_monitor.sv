// 帶 coverage 收集功能
class axi_monitor extends uvm_monitor;
    `uvm_component_utils(axi_monitor)

    virtual axi_if vif;
    uvm_analysis_port #(axi_txn) ap;

    covergroup axi_cov;
        option.per_instance = 1;
        burst_type_cp: coverpoint vif.AWBURST {
            bins fixed  = {2'b00};
            bins incr   = {2'b01};
            bins wrap   = {2'b10};
        }
        burst_len_cp: coverpoint vif.AWLEN {
            bins len_1  = {1};
            bins len_4  = {4};
            bins len_8  = {8};
            bins len_16 = {16};
        }
        qos_cp: coverpoint vif.AWQOS {
            bins qos0 = {0};
            bins qosF = {15};
        }
    endgroup

    function new(string name, uvm_component parent);
        super.new(name, parent);
        ap = new("ap", this);
        axi_cov = new();
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif))
            `uvm_fatal("AXI_MON", "No virtual interface")
    endfunction

    task run_phase(uvm_phase phase);
        axi_txn tr;
        forever begin
            wait (vif.AWVALID && vif.AWREADY);
            tr = axi_txn::type_id::create("tr", this);
            tr.id         = vif.AWID;
            tr.addr       = vif.AWADDR;
            tr.burst_len  = vif.AWLEN;
            tr.burst_type = vif.AWBURST;
            tr.qos        = vif.AWQOS;
            tr.is_write   = 1;

            axi_cov.sample(); // collect coverage
            ap.write(tr);
        end
    endtask
endclass
