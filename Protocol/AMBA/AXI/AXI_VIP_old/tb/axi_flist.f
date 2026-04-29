# RTL and Interface
./rtl/axi_slave_dut.sv

# UVM TB Components – Interfaces, Sequences
./tb/axi_if.sv
./tb/sequence/axi_txn.sv
./tb/sequence/axi_basic_seq.sv
./tb/sequence/axi_sequencer.sv

# UVM TB Components – Agents / Monitor / Driver
./tb/agent/axi_monitor.sv
./tb/agent/axi_driver.sv
./tb/agent/axi_agent.sv

# Scoreboard / Coverage
./tb/axi_scoreboard.sv
./tb/coverage.sv

# Environment / Test
./tb/axi_env.sv
./tb/axi_test.sv

# Top‐level testbench
./tb/top_tb.sv
