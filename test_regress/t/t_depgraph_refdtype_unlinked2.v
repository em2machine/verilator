// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

// DESCRIPTION: Verilator: Test for REFDTYPE not linked to type error
// This test reproduces a bug where a REFDTYPE for a file-scope typedef
// gets associated with a parameterized virtual class during DepGraph processing
//
// Pattern from aerial_wrap:
// - Include.sv has typedefs (Tag, RFTag) at file scope
// - clp_pkg.sv has a virtual class clp_c with parameters
// - TAG_ZERO localparam uses RFTag'(0) cast
// - The REFDTYPE for RFTag gets associated with clp_c during DepGraph capture

// File-scope typedefs (like Include.sv)
typedef logic[6:0] Tag;
typedef logic[5:0] RFTag;

// Virtual class with parameters (like clp_c in clp_pkg.sv)
// This class exists but doesn't contain the typedefs
virtual class clp_c #(parameter int cfg = 0);
    // Class has parameters but the typedefs are at file scope
endclass

// This localparam uses RFTag in a type cast
// The REFDTYPE for RFTag may get associated with clp_c during DepGraph
localparam Tag TAG_ZERO = {1'b1, RFTag'(0)};

// A struct that uses RFTag as a member type
typedef struct packed {
    RFTag tag;
    logic valid;
} RF_ReadReq;

module top;
    initial begin
        $display("TAG_ZERO = %b", TAG_ZERO);
        $display("RFTag width = %0d", $bits(RFTag));
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
