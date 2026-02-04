// File        :associative_arrays.sv
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :memory_model
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :This design models large memory efficiently by storing data only for addresses that are written.
module memory_model (
  input  logic clk,
  input  logic wr_en, rd_en,
  input  int   addr,
  input  int   wdata,
  output int   rdata
);

  int mem[int];   // Associative array memory

  // Write operation
  always_ff @(posedge clk) begin
    if (wr_en)
      mem[addr] = wdata;
  end

  // Read operation
  always_ff @(posedge clk) begin
    if (rd_en && mem.exists(addr))
      rdata <= mem[addr];
    else
      rdata <= 0;
  end

endmodule
