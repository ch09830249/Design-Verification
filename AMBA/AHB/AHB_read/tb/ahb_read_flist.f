# === RTL and Interface
./rtl/ahb_read_slave.sv

# === UVM TB Components
./tb/interface/ahb_if.sv
./tb/sequence/ahb_transaction.sv
./tb/sequence/ahb_read_sequence.sv
./tb/agent/ahb_read_monitor.sv
./tb/agent/ahb_read_driver.sv
./tb/agent/ahb_read_agent.sv
./tb/env/ahb_read_env.sv
./tb/test/ahb_read_test.sv

# === Top-level
./tb/ahb_read_top.sv
