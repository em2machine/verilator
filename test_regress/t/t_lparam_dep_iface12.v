// DESCRIPTION: Verilator: 4-level deep nested interface typedef with dependent localparams
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Todd Strader
// SPDX-License-Identifier: CC0-1.0

/*

- V3LinkDotDepGraph.cpp:582:DEPGRAPH: ========== DEPENDENCY TREE ==========
- V3LinkDotDepGraph.cpp:584:DEPGRAPH: Total nodes: 32  Iterations: 0
- V3LinkDotDepGraph.cpp:597:DEPGRAPH: t (top)
- V3LinkDotDepGraph.cpp:436:DEPGRAPH: ├── a_if__Cz1 : IFACE
- V3LinkDotDepGraph.cpp:491:DEPGRAPH: │   ├── GPARAM cfg [pending]
- V3LinkDotDepGraph.cpp:491:DEPGRAPH: │   ├── PARAMTYPE a_t [pending]
- V3LinkDotDepGraph.cpp:512:DEPGRAPH: │   └── b_inst : b_if__Cz1
- V3LinkDotDepGraph.cpp:563:DEPGRAPH: │       ├── GPARAM cfg=64'h200000003 [P]
- V3LinkDotDepGraph.cpp:563:DEPGRAPH: │       ├── LPARAM LP0=32'h6 [P]
- V3LinkDotDepGraph.cpp:436:DEPGRAPH: │       └── c_if__C6 : IFACE
- V3LinkDotDepGraph.cpp:491:DEPGRAPH: │           ├── GPARAM c_p [pending]
- V3LinkDotDepGraph.cpp:491:DEPGRAPH: │           ├── LPARAM LP0 = 32'hc [pending]
- V3LinkDotDepGraph.cpp:491:DEPGRAPH: │           ├── PARAMTYPE c_t [pending]
- V3LinkDotDepGraph.cpp:512:DEPGRAPH: │           └── d_inst : d_if__Dc
- V3LinkDotDepGraph.cpp:563:DEPGRAPH: │               ├── GPARAM d_p=32'hc [P]
- V3LinkDotDepGraph.cpp:563:DEPGRAPH: │               ├── LPARAM LP0=32'hd [P]
- V3LinkDotDepGraph.cpp:563:DEPGRAPH: │               └── TYPEDEF d_t[w1] [P]
- V3LinkDotDepGraph.cpp:436:DEPGRAPH: └── m__Cz1_Iz2 : MODULE
- V3LinkDotDepGraph.cpp:491:DEPGRAPH:     ├── GPARAM cfg [pending]
- V3LinkDotDepGraph.cpp:491:DEPGRAPH:     └── PARAMTYPE a_t [pending]
- V3LinkDotDepGraph.cpp:613:DEPGRAPH: ========== END TREE ==========

*/

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package scp;
  typedef struct packed {
    int unsigned ABits;
    int unsigned BBits;
  } cfg_t;
endpackage

// Level 4: innermost interface
interface d_if #(
  parameter d_p = 0
)();
  localparam int LP0 = d_p + 1;
  typedef logic [LP0-1:0] d_t;
endinterface

// Level 3
interface c_if #(
  parameter c_p = 0
)();
  localparam int LP0 = c_p * 2;
  d_if #(LP0) d_inst();
  typedef d_inst.d_t c_t;
endinterface

// Level 2
interface b_if #(
  parameter scp::cfg_t cfg = 0
)();
  localparam int LP0 = cfg.ABits * cfg.BBits;
  c_if #(LP0) c_inst();
  typedef c_inst.c_t b_t;
endinterface

// Level 1: outermost interface
interface a_if #(
  parameter scp::cfg_t cfg = 0
)();
  b_if #(cfg) b_inst();
  typedef b_inst.b_t a_t;
endinterface

module m #(parameter scp::cfg_t cfg=0) (
  a_if io
);

  typedef io.a_t a_t;

  initial begin
    #1;
    // cfg.ABits=2, cfg.BBits=3
    // b_if: LP0 = 2*3 = 6
    // c_if: c_p=6, LP0 = 6*2 = 12
    // d_if: d_p=12, LP0 = 12+1 = 13
    // d_t is 13 bits
    `checkd($bits(a_t), 13);
  end
endmodule

module t();
  localparam scp::cfg_t cfg = '{
    ABits : 2
    ,BBits : 3
  };

  a_if #(cfg) a_io ();

  m #(cfg) m_inst(
    .io(a_io)
  );

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
