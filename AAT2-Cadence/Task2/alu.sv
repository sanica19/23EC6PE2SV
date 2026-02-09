//Design
module alu (
  alu_if.DUT alu_if
);

  typedef enum logic [1:0] {
    ADD = 2'b00,
    SUB = 2'b01,
    MUL = 2'b10,
    XOR = 2'b11
  } opcode_t;

  always_ff @(posedge alu_if.clk) begin
    case (alu_if.opcode)
      ADD: alu_if.result <= alu_if.a + alu_if.b;
      SUB: alu_if.result <= alu_if.a - alu_if.b;
      MUL: amodule alu (
  alu_if.DUT alu_if
);

  typedef enum logic [1:0] {
    ADD = 2'b00,
    SUB = 2'b01,
    MUL = 2'b10,
    XOR = 2'b11
  } opcode_t;

  always_ff @(posedge alu_if.clk) begin
    case (alu_if.opcode)
      ADD: alu_if.result <= alu_if.a + alu_if.b;
      SUB: alu_if.result <= alu_if.a - alu_if.b;
      MUL: alu_if.result <= alu_if.a * alu_if.b;
      XOR: alu_if.result <= alu_if.a ^ alu_if.b;

      // Unreachable default (all 2-bit values covered)
      // pragma coverage off
      default: alu_if.result <= '0;
      // pragma coverage on
    endcase
  end

endmodule
lu_if.result <= alu_if.a * alu_if.b;
      XOR: alu_if.result <= alu_if.a ^ alu_if.b;

      // Unreachable default (all 2-bit values covered)
      // pragma coverage off
      default: alu_if.result <= '0;
      // pragma coverage on
    endcase
  end

endmodule

//Test Bench
module tb_alu (alu_if.TB alu_if);

  typedef enum logic [1:0] {
    ADD = 2'b00,
    SUB = 2'b01,
    MUL = 2'b10,
    XOR = 2'b11
  } opcode_t;

  class alu_trans;
    rand logic [7:0] a, b;
    rand opcode_t opcode;

    // MUL must occur at least 20%
    constraint opcode_dist {
      opcode dist {
        ADD := 30,
        SUB := 30,
        MUL := 20,
        XOR := 20
      };
    }
  endclass

  alu_trans tr;

  covergroup alu_cg;
    coverpoint alu_if.opcode {
      bins add = {ADD};
      bins sub = {SUB};
      bins mul = {MUL};
      bins xor_ = {XOR};
    }
  endgroup

  alu_cg cg;

  // ============================
  // VCD DUMP (SimVision)
  // ============================
  initial begin
    $dumpfile("alu_wave.vcd");
    $dumpvars(0, top);
  end

  // ============================
  // TEST SEQUENCE
  // ============================
  initial begin
    tr = new();
    cg = new();

    repeat (100) begin
      assert(tr.randomize());

      alu_if.a      = tr.a;
      alu_if.b      = tr.b;
      alu_if.opcode = tr.opcode;

      @(posedge alu_if.clk);
      cg.sample();

      $display("A=%0d B=%0d OPCODE=%0d RESULT=%0d",
               alu_if.a, alu_if.b, alu_if.opcode, alu_if.result);
    end

    $display("Coverage = %0.2f %%", cg.get_coverage());
    $finish;
  end

endmodule

//Interface

interface alu_if (input logic clk);

  logic [7:0] a, b;
  logic [7:0] result;
  logic [1:0] opcode;

  modport DUT (
    input  a, b, opcode, clk,
    output result
  );

  modport TB (
    output a, b, opcode,
    input  result, clk
  );

endinterface

//top module

module top;

  logic clk;
  always #5 clk = ~clk;

  alu_if alu_if (clk);

  alu dut (
    .alu_if(alu_if)
  );

  tb_alu tb (
    .alu_if(alu_if)
  );

  initial clk = 0;

endmodule
