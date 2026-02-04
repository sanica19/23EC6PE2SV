// File        :sva
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :SVA
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :Design delays the request by two clock cycles to generate the grant signal.

module handshake_design (
  input  logic clk, rst,
  input  logic req,
  output logic gnt
);

  logic [1:0] delay;

  always_ff @(posedge clk) begin
    if (rst) begin
      delay <= 0;
      gnt   <= 0;
    end else begin
      delay <= {delay[0], req}; // shift register delay
      gnt   <= delay[1];        // grant after 2 cycles
    end
  end

endmodule


 
