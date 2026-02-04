//------------------------------------------------------------------------------
//File       : dual_port_ram.sv
//Author     : Sanica M S/1BM23EC229
//Created    : 04-02-2026
//Module     : dual_port_ram
//Project    : SystemVerilog and Verification (23EC6PE2SV)
//Faculty    : Prof. Ajaykumar Devarapalli
//Description: Dual Port RAM with Port A (Write) and Port B (Read).
//             Parameters allow for flexible Address and Data widths.
//------------------------------------------------------------------------------
module dual_port_ram #(
    parameter ADDR_WIDTH = 4,
    parameter DATA_WIDTH = 8
)(
    input  wire                   clk,
    // Port A (Write)
    input  wire                   we_a,
    input  wire [ADDR_WIDTH-1:0]  addr_a,
    input  wire [DATA_WIDTH-1:0]  wdata_a,
    // Port B (Read)
    input  wire [ADDR_WIDTH-1:0]  addr_b,
    output reg  [DATA_WIDTH-1:0]  rdata_b
);

    reg [DATA_WIDTH-1:0] mem [0:(1<<ADDR_WIDTH)-1];

    always @(posedge clk) begin
        if (we_a)
            mem[addr_a] <= wdata_a;

        rdata_b <= mem[addr_b]; // synchronous read
    end
endmodule
