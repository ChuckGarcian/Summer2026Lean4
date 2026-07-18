local show_answers = false

function GetMetadata(meta)
    if meta.show_answers then
        show_answers = true
    end
end

-- Function to check if a block or inline is one of our LaTeX markers
local function is_marker(el, marker)
    if el.t == "RawBlock" or el.t == "RawInline" then
        return el.format == "tex" and el.text:match(marker)
    end
    -- Also check if a paragraph starts with the marker
    if el.content then
        for _, inline in ipairs(el.content) do
            if (inline.t == "RawInline" or inline.t == "RawBlock") and inline.text:match(marker) then
                return true
            end
        end
    end
    return false
end

function Pandoc(doc)
    if show_answers then return doc end

    local new_blocks = {}
    local skipping = false

    for _, block in ipairs(doc.blocks) do
        -- If we hit an \answer, start skipping
        if is_marker(block, "\\answer") then
            skipping = true
        -- If we hit a \question, stop skipping
        elseif is_marker(block, "\\question") then
            skipping = false
        end

        -- Logic: Keep the block if we aren't skipping.
        -- We ALWAYS keep \question blocks so the question text stays.
        if not skipping or is_marker(block, "\\question") then
            table.insert(new_blocks, block)
        end
    end

    return pandoc.Pandoc(new_blocks, doc.meta)
end

return {{Meta = GetMetadata}, {Pandoc = Pandoc}}