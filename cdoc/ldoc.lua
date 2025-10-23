--ldoc
--[[
% Lua documentation tool

The `ldoc` tool converts a Lua code file with intermixed text
documentation (in comments) into a markup language (Markdown).
A printer object provides methods to print lines of text and code,
and a main routine is responsible for deciding which is which,
and if anything should be printed at all.

# Printers

Each printer object is responsible for implementing `print_code` and
`print_line` routines that print code lines and ordinary text lines.

## Printer base class

A generic printer class defines the `new` method used to actually
instantiate new printers.
--]]

Printer = {}
Printer.__index = Printer

function Printer:new(tbl)
   tbl = tbl or {}
   tbl.__index = tbl
   setmetatable(tbl, self)
   return tbl
end

--[[
## Generic Markdown printer

The default printer generates standard Markdown.  Code is indented
four spaces; everything else passes through unaltered.
--]]

local MarkdownPrinter = Printer:new()

function MarkdownPrinter:print_code(line)
   self.fp:write("    " .. line .. "\n")
end

function MarkdownPrinter:print_text(line)
   self.fp:write(line .. "\n")
end

--[[
## Pandoc Markdown printer

The Pandoc processor recognizes an extension where code regions
are demarcated by lines of tildes.  Using this convention, we can
pass through labels saying that we're processing Lua code.

We keep track of whether or not we're in a code block with the
`in_code` member variable.  If we're not in a code block, we start one
with the first non-blank code line we encounter.  We skip blank lines
to avoid completely empty code blocks.  If we are in a code block, we
exit it the next time we see a text line.
--]]

local PandocPrinter = Printer:new()

function PandocPrinter:print_code(line)
   if not self.in_code and string.find(line, "%S") then
      self.fp:write("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~")
      if self.attribs then 
         self.fp:write("{" .. self.attribs .. "}") 
      end
      self.fp:write("\n")
      self.in_code = true
   end
   if self.in_code then self.fp:write(line .. "\n") end
end

function PandocPrinter:print_text(line)
   if self.in_code then
      self.fp:write("~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n")
      self.in_code = false
   end
   self.fp:write(line .. "\n")
end

--[[
## GitHub Markdown printer with Liquid

The GitHub Liquid templating engine can do syntax highlighting with 
Pygments using highlight tags.  Use the `highlight` argument to specify
the language.
--]]

local GithubPrinter = Printer:new()

function GithubPrinter:print_code(line)
   if not self.in_code and string.find(line, "%S") then
      if not self.highlight then
         error("highlight must be defined for Github markdown")
      end
      self.fp:write("\n{% highlight " .. self.highlight .. " %}\n")
      self.in_code = true
   end
   if self.in_code then self.fp:write(line .. "\n") end
end

function GithubPrinter:print_text(line)
   if self.in_code then
      self.fp:write("{% endhighlight %}\n\n")
      self.in_code = false
   end
   self.fp:write(line .. "\n")
end

--[[
## Quarto Markdown printer

Quarto fences code with triple backticks.  Use the `highlight` argument
to specify the language for highlighting, as with GitHub Liquid templating.
Use the `exec` argument to compile to something that will actually be run
via the Quarto processor.
--]]

local QuartoPrinter = Printer:new()

function QuartoPrinter:print_code(line)
   if not self.in_code and string.find(line, "%S") then
      self.fp:write("\n```")
      if self.exec then
         self.fp:write("{" .. self.exec .. "}")
      elseif self.highlight then
         self.fp:write("{." .. self.highlight .. "}")
      end
      self.fp:write("\n")
      self.in_code = true
   end
   if self.in_code then self.fp:write(line .. "\n") end
end

function QuartoPrinter:print_text(line)
   if self.in_code then
      self.fp:write("```\n\n")
      self.in_code = false
   end
   self.fp:write(line .. "\n")
end

--[[
## LaTeX printer

The LaTeX processor does two things.  First, it uses the Markdown
convention and wrap anything in backticks in a `verb` environment.
Second, it wraps any code lines in a `verbatim` environment.  You
could do something fancier with one of the listings environments, but
I prefer to keep things simple.  In fact, I rather like just using
Markdown.
--]]

local LatexPrinter = Printer:new()

function LatexPrinter:print_code(line)
   if not self.in_code and string.find(line, "%S") then
      self.fp:write("\n\\begin{verbatim}\n")
      self.in_code = true
   end
   if self.in_code then self.fp:write(line .. "\n") end
end

function LatexPrinter:print_text(line)
   if self.in_code then
      self.fp:write("\\end{verbatim}\n")
      self.in_code = false
   end
   line = string.gsub(line, "%`([^%`]+)%`", "\\verb|%1|")
   self.fp:write(line .. "\n")
end

--[[
# Processing input files

The `ldoc` documentation tool can be toggled on or off with special
comment lines consisting of the text `ldoc`.  Comments with just the
text `ldoc on` or `ldoc off` turn the documentation on or off; `ldoc`
with nothing else toggles the current state.  By default,
documentation is assumed to be turned off.  When documentation is
turned on, text in block comments is sent directly to the output,
while text outside of comment blocks is formatted as code.

## Lua input files

In Lua, we treat block comments as text and everything outside of
block comments as code.  We skip the lines where the comment begins
and ends.  In order to toggle the documentation tool state, we use
ordinary (not block) comment lines.
--]]

local function ldoc(lname,printer)
   local printing, in_text
   for line in io.lines(lname) do
      if string.find(line, "%s*%-%-ldoc%s+on") == 1 then
         printing = true
      elseif string.find(line, "%s*%-%-ldoc%s+off") == 1 then
         printing = false
      elseif string.find(line, "%s*%-%-ldoc") == 1 then
         printing = not printing
      elseif string.find(line, "%s*%-%-%[%[") == 1 then
         in_text = true
      elseif string.find(line, "%s*%-%-%]%]") == 1 then
         in_text = false
      elseif printing then
         if in_text then printer:print_text(line)
         else            printer:print_code(line)
         end
      end
   end
   printer:print_text("")
end

--[[
## Processing C input files

The C documentation tool can be toggled on or off with a single line
comment (C or C++ style).  Subsequently, C-style comment blocks
beginning at the start of the line with two stars (`/**`) are treated
as the beginning of documentation blocks, and the corresponding
end-of-comment lines are treated as the end of documentation blocks.
If there is a leading space-asterisk-space in text lines, we strip
it away before processing.
--]]

local function cdoc(lname,printer)
   local printing, in_text
   for line in io.lines(lname) do
      if string.find(line, "/%*%s*ldoc on%s%*/") == 1 or
         string.find(line, "//%s*ldoc on%s*$") == 1 then
         printing = true
      elseif string.find(line, "/%*%s*ldoc off%s%*/") == 1 or
         string.find(line, "//%s*ldoc off%s*$") == 1 then
         printing = false
      elseif string.find(line, "/%*%s*ldoc%s*/") == 1 or
         string.find(line, "//%s*ldoc%s*$") == 1 then
         printing = not printing
      elseif string.find(line, "/%*%*%s*$") == 1 then
         in_text = true
      elseif in_text and string.find(line, "%s*%*/$") == 1 then
         in_text = false
      elseif printing then
         if in_text then printer:print_text(string.gsub(line, "^ %* ", ""))
         else            printer:print_code(line)
         end
      end
   end
   printer:print_text("")
end

--[[
## Processing Julia input files

In Julia, we treat block comments as text and everything outside of
block comments as code.  We skip the lines where the comment begins
and ends.  In order to toggle the documentation tool state, we use
ordinary (not block) comment lines.
--]]

local function jdoc(lname,printer)
   local printing, in_text
   for line in io.lines(lname) do
      if string.find(line, "%s*#ldoc%s+on") == 1 then
         printing = true
      elseif string.find(line, "%s*#ldoc%s+off") == 1 then
         printing = false
      elseif string.find(line, "%s*#ldoc") == 1 then
         printing = not printing
      elseif string.find(line, "%s*#=") == 1 then
         in_text = true
      elseif string.find(line, "%s*=#") == 1 then
         in_text = false
      elseif printing then
         if in_text then printer:print_text(line)
         else            printer:print_code(line)
         end
      end
   end
   printer:print_text("")
end

--[[
## Processing MATLAB input files

The MATLAB documentation tool can be toggled on or off with a line
beginning with `%ldoc`.  Subsequently, comment blocks beginning with
a double percent are treated as the beginning of documentation blocks,
which are ended at the first non-comment line.
--]]

local function mdoc(lname,printer)
   local printing, in_text
   for line in io.lines(lname) do
      if string.find(line, "%%ldoc on") == 1 then
         printing = true
      elseif string.find(line, "%%ldoc off") == 1 then
         printing = false
      elseif string.find(line, "%%ldoc") == 1 then
         printing = not printing
      elseif string.find(line, "%%%%%s*$") == 1 then
         in_text = true
      elseif in_text and string.find(line, "%%") ~= 1 then
         in_text = false
      elseif printing then
         if in_text then printer:print_text(string.gsub(line, "^%%%s?", ""))
         else            printer:print_code(line)
         end
      end
   end
   printer:print_text("")
end

--[[
## Processing shell input files

The shell-style documentation tool can be toggled with a line
beginning with `#ldoc`.  Subsequently, comment blocks beginning with
a `##` are treated as the beginning of documentation blocks,
which are ended at the first non-comment line.
--]]

local function shdoc(lname,printer)
   local printing, in_text
   for line in io.lines(lname) do
      if string.find(line, "#ldoc on") == 1 then
         printing = true
      elseif string.find(line, "#ldoc off") == 1 then
         printing = false
      elseif string.find(line, "#ldoc") == 1 then
         printing = not printing
      elseif string.find(line, "##%s*$") == 1 then
         in_text = true
      elseif in_text and string.find(line, "#") ~= 1 then
         in_text = false
      elseif printing then
         if in_text then printer:print_text(string.gsub(line, "^#%s?", ""))
         else            printer:print_code(line)
         end
      end
   end
   printer:print_text("")
end

--[[
# Main routine

The `main` routine runs a list of files through the `ldoc` processor.
If the argument list includes something of the form `-o ofname`, then
output is directed to `ofname`; otherwise, output goes to the standard
output.  We select a printer using the `-p` option; choices are
`markdown` and `pandoc`.
--]]

local printers = {
   markdown = MarkdownPrinter,
   pandoc   = PandocPrinter,
   quarto   = QuartoPrinter,
   latex    = LatexPrinter,
   github   = GithubPrinter
}

local processors = {
   lua = ldoc,
   c   = cdoc,
   h   = cdoc,
   cc  = cdoc,
   cpp = cdoc,
   C   = cdoc,
   jl  = jdoc,
   m   = mdoc,
   sh  = shdoc,
   csh = shdoc,
   zsh = shdoc,
   py  = shdoc
}

local function main(args)

   local oname               -- Output file name
   local lname               -- Language name (if not by extension)
   local pname = "markdown"  -- Printer name
   local fnames = {}         -- Input file names
   local skip = 0            -- Arguments to skip

   -- Printer arguments
   pargs = {}
   
   -- Option processing
   for i=1,#args do
      local function process_flag(k)
         skip = k
         return args[i+1]
      end
      if     skip > 0        then skip = skip-1
      elseif args[i] == "-o" then oname = process_flag(1)
      elseif args[i] == "-p" then pname = process_flag(1)
      elseif args[i] == "-l" then lname = process_flag(1)
      else
         local parg = string.match(args[i], "^%-(%w+)")
         if parg then
            pargs[parg] = process_flag(1)
         else
            table.insert(fnames, args[i])
         end
      end
   end

   -- Check argument correctness
   assert(printers[pname], "Unknown printer: " .. pname)

   -- Set up printer and write files
   pargs.fp = (oname and io.open(oname, "w+")) or io.stdout
   local printer = printers[pname]:new(pargs)
   for i,fname in ipairs(fnames) do 
      local file_lname = lname or string.match(fname, "%.(%w+)$")
      local processor = processors[file_lname]
      if processor then 
         processor(fname,printer) 
      else
         print("Unknown language, skipping: ", fname)
      end
   end
   if pargs.fp ~= io.stdout then pargs.fp:close() end

end

main {...}
