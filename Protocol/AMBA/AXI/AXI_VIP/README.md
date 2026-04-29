# 📘 AXI UVM VIP Description

## 🧩 Module Overview

This project implements a configurable and reusable AXI4 (Advanced eXtensible Interface) UVM Verification IP based on the AMBA® AXI4 protocol specification (IHI 0022H).
It supports three modes of operation — **master VIP**, **slave VIP**, and **loopback testbench** — through flexible configuration.

The VIP includes layered base components, driver/monitor/sequencer agents, protocol timing assertions (SystemVerilog Assertions), optional bus functional models (BFMs), and reference model support.
It is designed to validate both master and slave DUTs by instantiating the corresponding passive or active agent, and can be used for directed or random stimulus generation.

### Supported Features

- AXI4 master transactions: read/write burst stimulus generation with configurable `AWLEN`/`ARLEN`, `AWSIZE`/`ARSIZE`, `AWBURST`/`ARBURST`
- AXI4 slave response handling: data return, WSTRB byte-enable, and memory emulation
- Five independent channel handshaking: AW, W, B, AR, R — write and read paths fully decoupled
- Burst type support: FIXED, INCR, WRAP
- Out-of-order read response support via transaction ID (`ARID`/`RID`)
- Loopback test support between master and slave agents
- Built-in SystemVerilog Assertions (SVA) for protocol handshake and timing checks
- UVM scoreboard and passive agent monitoring support
- Functional coverage for address, burst, size, length, ID, and response signals
- Optional BFMs for standalone integration without UVM

---

## 🔧 I/O Signals

### AW Channel (Write Address)

| Signal     | Direction (Master) | Width           | Description              |
|------------|--------------------|-----------------|--------------------------|
| `ACLK`     | Input              | 1               | AXI clock                |
| `ARESETn`  | Input              | 1               | Active-low reset         |
| `AWID`     | Output             | `D_ID_WIDTH     | Write address ID         |
| `AWADDR`   | Output             | `D_ADDR_WIDTH   | Write address            |
| `AWLEN`    | Output             | 8               | Burst length (beats - 1) |
| `AWSIZE`   | Output             | 3               | Burst size               |
| `AWBURST`  | Output             | 2               | Burst type               |
| `AWVALID`  | Output             | 1               | Write address valid      |
| `AWREADY`  | Input              | 1               | Write address ready      |

### W Channel (Write Data)

| Signal    | Direction (Master) | Width             | Description         |
|-----------|--------------------|-------------------|---------------------|
| `WDATA`   | Output             | `D_DATA_WIDTH     | Write data          |
| `WSTRB`   | Output             | `D_DATA_WIDTH/8   | Write byte strobe   |
| `WLAST`   | Output             | 1                 | Last beat indicator |
| `WVALID`  | Output             | 1                 | Write data valid    |
| `WREADY`  | Input              | 1                 | Write data ready    |

### B Channel (Write Response)

| Signal    | Direction (Master) | Width         | Description            |
|-----------|--------------------|---------------|------------------------|
| `BID`     | Input              | `D_ID_WIDTH   | Write response ID      |
| `BRESP`   | Input              | 2             | Write response         |
| `BVALID`  | Input              | 1             | Write response valid   |
| `BREADY`  | Output             | 1             | Write response ready   |

### AR Channel (Read Address)

| Signal     | Direction (Master) | Width          | Description             |
|------------|--------------------|----------------|-------------------------|
| `ARID`     | Output             | `D_ID_WIDTH    | Read address ID         |
| `ARADDR`   | Output             | `D_ADDR_WIDTH  | Read address            |
| `ARLEN`    | Output             | 8              | Burst length (beats -1) |
| `ARSIZE`   | Output             | 3              | Burst size              |
| `ARBURST`  | Output             | 2              | Burst type              |
| `ARVALID`  | Output             | 1              | Read address valid      |
| `ARREADY`  | Input              | 1              | Read address ready      |

### R Channel (Read Data)

| Signal    | Direction (Master) | Width          | Description          |
|-----------|--------------------|----------------|----------------------|
| `RID`     | Input              | `D_ID_WIDTH    | Read data ID         |
| `RDATA`   | Input              | `D_DATA_WIDTH  | Read data            |
| `RRESP`   | Input              | 2              | Read response        |
| `RLAST`   | Input              | 1              | Last beat indicator  |
| `RVALID`  | Input              | 1              | Read data valid      |
| `RREADY`  | Output             | 1              | Read data ready      |

---

## 🔁 AXI4 Protocol Behavior

- **Write path (AW → W → B)**:
  - Master asserts `AWVALID` with valid `AWADDR`, `AWID`, `AWLEN`, `AWSIZE`, `AWBURST`.
  - Slave responds with `AWREADY` to complete the AW handshake.
  - Master drives `WDATA`/`WSTRB` beat by beat, asserting `WLAST` on the final beat.
  - Slave responds with `WREADY` each beat; after `WLAST`, slave asserts `BVALID` with `BRESP`.
  - Master asserts `BREADY` to complete the B handshake and finish the write transaction.

- **Read path (AR → R)**:
  - Master asserts `ARVALID` with valid `ARADDR`, `ARID`, `ARLEN`, `ARSIZE`, `ARBURST`.
  - Slave responds with `ARREADY` to complete the AR handshake.
  - Slave returns `RDATA` beat by beat, asserting `RLAST` on the final beat; each beat carries `RRESP` and `RID`.
  - Master asserts `RREADY` each beat to complete the R handshake.

- **Channel independence**:
  - AW and AR channels are fully decoupled — write and read transactions may be in-flight simultaneously.
  - W channel may be accepted before or after AW channel depending on slave implementation.

- **Burst types**:
  - `FIXED` (2'b00): address does not increment, used for FIFOs.
  - `INCR`  (2'b01): address increments each beat, most common.
  - `WRAP`  (2'b10): address wraps at a boundary, used for cache line fills.

- **Error Response**:
  - Slave returns `BRESP`/`RRESP` = `2'b10` (SLVERR) to indicate a transfer error.
  - Response is valid only when the corresponding `BVALID`/`RVALID` and `BREADY`/`RREADY` are both high.

---

## 📁 Directory Structure

```
AXI_VIP/
|
├── bfm/
│   └── axi_slave_bfm.sv
│
├── seq/
│   └── axi_master_seq.sv
│
├── test/
│   └── axi_basic_rw_test.sv
│
├── top/
│   └── sim_top.sv
│
├── vip/
│   ├── base/
│   │   ├── axi_agent_base.sv
│   │   ├── axi_driver_base.sv
│   │   └── axi_monitor_base.sv
│   │
│   ├── common/
│   │   ├── axi_coverage.sv
│   │   ├── axi_define.svh
│   │   ├── axi_env.sv
│   │   ├── axi_package.svh
│   │   ├── axi_scoreboard.sv
│   │   └── axi_seq_item.sv
│   │
│   ├── interface/
│   │   └── axi_interface.sv
│   │
│   ├── master/
│   │   ├── axi_master_agent.sv
│   │   ├── axi_master_driver.sv
│   │   └── axi_master_monitor.sv
│   │
│   ├── slave/
│   │   ├── axi_slave_agent.sv
│   │   ├── axi_slave_driver.sv
│   │   └── axi_slave_monitor.sv
│   │
│   └── sva/
│       ├── axi_protocol_sva.sv
│       └── bind_axi_protocol_sva.sv
│
├── axi_vip.f
│
└── README.md
```

## Simulation
```
xrun -f axi_vip.f -access +r +UVM_TESTNAME=axi_basic_rw_test
```
