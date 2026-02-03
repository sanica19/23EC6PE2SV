//------------------------------------------------------------------------------
//File       : priority_enc.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 03-02-2026
//Module     : priority_enc
//Project    : SystemVerilog and Verification (23EC6PE2SV),
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: 4:2 Priority Encoder used for basic functional coverage example.
//------------------------------------------------------------------------------

module priority_enc(
  input logic [3:0] in,
  output logic [1:0] out,
  output logic valid
);
  always_comb begin
    valid = 1;

    casez(in)
      4'b1???: out = 2'b11; 
      4'b01??: out = 2'b10;
      4'b001?: out = 2'b01;
      4'b0001: out = 2'b00;
      default: begin 
        out = 2'b00; 
        valid = 0;
      end
    endcase
  end
endmodule
