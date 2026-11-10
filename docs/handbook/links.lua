local source_path, repository_source

local function resolve(path)
  local parts = {}
  local joined = pandoc.path.directory(source_path) .. "/" .. path
  for part in joined:gmatch("[^/]+") do
    if part == ".." then
      assert(#parts > 0, "Link escapes the repository: " .. path)
      table.remove(parts)
    elseif part ~= "." then
      table.insert(parts, part)
    end
  end
  return table.concat(parts, "/")
end

-- Resolve links relative to the original Markdown, before it was staged.
local function rewrite_link(link)
  local target = link.target
  if target:match("^[%a][%w+.-]*:") or target:match("^[#/]") then
    return nil
  end
  local path, suffix = target:match("^([^?#]+)(.*)$")
  if not path then
    return nil
  end
  local resolved = resolve(path)
  if resolved == "README.md" then
    link.target = "research-plan.html" .. suffix
  elseif resolved == "docs/README.md" then
    link.target = "index.html" .. suffix
  elseif resolved:match("^docs/[^/]+%.md$") then
    link.target = pandoc.path.filename(resolved):gsub("%.md$", ".html") .. suffix
  elseif resolved:match("^ProjectAInos/.*%.lean$") or resolved == "ProjectAInos.lean" then
    link.target = "api/" .. resolved:gsub("%.lean$", ".html") .. suffix
  else
    link.target = repository_source .. resolved .. suffix
  end
  return link
end

return {
  { Meta = function(meta)
    source_path = pandoc.utils.stringify(meta["source-path"])
    repository_source = pandoc.utils.stringify(meta["repository-source"])
  end },
  { Link = rewrite_link },
}
